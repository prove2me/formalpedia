-- Prove2me | Theorems.Thm_CoverModular_Supplement_lemma_3
-- name    : CoverModular.Supplement.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:17:32.206447+00:00
-- url     : https://prove2.me/theorems/5eda11a8-b27f-5e46-ab25-b270c3264106
-- title:
--   Lemma 3 — $\alpha^{\mathcal S\cup\mathcal T}=\bar\alpha^{\mathcal S}+\sum_k\alpha^k$ is dual feasible and $h(\mathcal S\cup\mathcal T)\le\bar a\,h(\mathcal S)+\sum_{k}\sum_ib_i\alpha^k_i$
-- statement:
--   Consider the LP-based set function $h$ of (17). Assume that the constraint matrix $A=[a_{ij}]$ is non-negative and integral, that $p\ge0$, and that $b_i>0$ for every $i$ (Assumption 1 together with the standing assumption of Appendix A.3). Let $\bar a=\max_j\sum_ia_{ij}$ be the column sparsity. Fix $\mathcal S,\mathcal T\subseteq\mathcal U$ and an optimal solution $x^{\mathcal S}$ of (17) for $\mathcal A=\mathcal S$, and put $\bar\alpha^{\mathcal S}_i=\sum_jp_ja_{ij}x^{\mathcal S}_j/b_i$. For each $k\in\mathcal S\cup\mathcal T$, let $\alpha^k$ be an optimal solution of the auxiliary LP
--
--   $$
--   \min_\alpha\ \sum_ib_i\alpha_i\quad\text{s.t.}\quad\sum_ia_{ij}\alpha_i\ge p_j-\sum_ia_{ij}\bar\alpha^{\mathcal S}_i\ (j\in J_k),\qquad\alpha_i\ge0\ \ \forall i,\tag{29}
--   $$
--
--   and let
--
--   $$
--   \alpha^{\mathcal S\cup\mathcal T}_i:=\bar\alpha^{\mathcal S}_i+\sum_{k\in\mathcal S\cup\mathcal T}\alpha^k_i\quad\forall i.\tag{30}
--   $$
--
--   Then:
--
--   1. $\alpha^{\mathcal S\cup\mathcal T}$ is a feasible solution of the dual (28) with $\mathcal A=\mathcal S\cup\mathcal T$;
--   2. the following inequality holds:
--
--   $$
--   h(\mathcal S\cup\mathcal T)\le\bar a\,h(\mathcal S)+\sum_{k\in\mathcal S\cup\mathcal T}\sum_ib_i\alpha^k_i.\tag{31}
--   $$
--
--   This is the dual-construction half of the proof of Theorem 2. Lemma 4 then bounds each term $\sum_ib_i\alpha^k_i$ by the marginal gain $h(\mathcal S\cup\{k\})-h(\mathcal S)$.
--
--   **Formalization Note** The family $(\alpha^k)$ is any function of $k$ that is optimal for (29) at every $k\in\mathcal S\cup\mathcal T$. $\mathcal S$ and $\mathcal T$ are finite sets. Since $b>0$, the division defining $\bar\alpha^{\mathcal S}$ is the paper's.
--
--   Differences from the source:
--   - encoding: A non-negative integral matrix (Assumption 1) → a natural-number matrix cast to ℝ; reason: same instances
--   - reading: "the optimal solution" x^S of (17) and α^k of (29) → every choice of optimal solutions; reason: the page writes "the" but the optimum need not be unique, and the statement holds for each choice
--   - encoding: S, T ⊂ U (arbitrary subsets) → finite sets S, T : Finset U; reason: the sums over S ∪ T in (30)–(31) are finite sums, so the paper's S ∪ T is finite
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, Lemma 3, p.41 (displays (29)–(31)); Assumption 1, p.23; standing assumption b > 0, p.40

import Mathlib
import Definitions.Def_CoverModular_Supplement_h
import Definitions.Def_CoverModular_Supplement_colSparsity
import Definitions.Def_CoverModular_Supplement_IsOptimalPrimal
import Definitions.Def_CoverModular_Supplement_IsDualFeasible
import Definitions.Def_CoverModular_Supplement_alphaBar
import Definitions.Def_CoverModular_Supplement_IsOptimalAux

namespace CoverModular.Supplement

/-- **Lemma 3** (DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*,
SSRN 3844987, Appendix A.3, Lemma 3, p.41). Under Assumption 1 and the Appendix A.3 standing
assumption `b > 0`, fix sets `S, T ⊆ U`, an optimal solution `x^S` of (17) for `A = S`, and for
each `k ∈ S ∪ T` an optimal solution `α^k` of the auxiliary LP (29) built from `ᾱ^S`. Then
`α^{S∪T}_i := ᾱ^S_i + ∑_{k ∈ S ∪ T} α^k_i` (30) is feasible for the dual (28) with `A = S ∪ T`,
and `h(S ∪ T) ≤ ā h(S) + ∑_{k ∈ S ∪ T} ∑_i b_i α^k_i` (31).

**Formalization Note** `a : Fin m → Fin n → ℕ` encodes "non-negative integral"; `b > 0`
subsumes `b ≥ 0`. The family `α : U → Fin m → ℝ` is constrained only at `k ∈ S ∪ T`. -/
theorem lemma_3 {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ) (p : Fin n → ℝ)
    (b : Fin m → ℝ) (J : U → Finset (Fin n)) (hp : ∀ j, 0 ≤ p j) (hb : ∀ i, 0 < b i)
    (S T : Finset U) (xS : Fin n → ℝ) (hxS : IsOptimalPrimal a p b J S xS)
    (α : U → Fin m → ℝ)
    (hα : ∀ k ∈ S ∪ T, IsOptimalAux a p b J (alphaBar a p b xS) k (α k)) :
    IsDualFeasible a p J (S ∪ T) (fun i => alphaBar a p b xS i + ∑ k ∈ S ∪ T, α k i) ∧
      h a p b J (S ∪ T) ≤
        (colSparsity a : ℝ) * h a p b J S + ∑ k ∈ S ∪ T, ∑ i, b i * α k i := by sorry

end CoverModular.Supplement
