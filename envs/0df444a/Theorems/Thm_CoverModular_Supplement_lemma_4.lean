-- Prove2me | Theorems.Thm_CoverModular_Supplement_lemma_4
-- name    : CoverModular.Supplement.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:18:05.480443+00:00
-- url     : https://prove2.me/theorems/ff02b054-20fe-4e21-a0e9-db8ba17ced3f
-- title:
--   Lemma 4 — the optimal value of (29) bounds the marginal gain from below, $\sum_ib_i\alpha^k_i+h(\mathcal S)\le h(\mathcal S\cup\{k\})$
-- statement:
--   Consider the LP-based set function $h$ of (17). Assume that $A=[a_{ij}]$ is non-negative and integral, that $p\ge0$, and that $b_i>0$ for every $i$ (Assumption 1 together with the standing assumption of Appendix A.3). Fix $\mathcal S,\mathcal T\subseteq\mathcal U$ and $k\in\mathcal S\cup\mathcal T$. Let $x^{\mathcal S}$ be an optimal solution of (17) for $\mathcal A=\mathcal S$, let $\bar\alpha^{\mathcal S}_i=\sum_jp_ja_{ij}x^{\mathcal S}_j/b_i$, and let $\alpha^k$ be an optimal solution of the auxiliary LP (29) for $k$. Then
--
--   $$
--   \sum_ib_i\alpha^k_i+h(\mathcal S)\le h(\mathcal S\cup\{k\}).
--   $$
--
--   So the optimal value of the small LP (29), which involves only the variables in $J_k$, is a lower bound on the marginal gain $h(\mathcal S\cup\{k\})-h(\mathcal S)$. With Lemma 3 this gives the $\bar a$-cover modularity of $h$ in Theorem 2, and it also makes $\sum_ib_i\alpha^k_i$ usable as a surrogate for the marginal gain in greedy-type heuristics.
--
--   **Formalization Note** $\mathcal S\cup\{k\}$ is `insert k S`. The set $\mathcal T$ only locates $k$, as on the page. No boundedness hypothesis is needed for $h(\mathcal S\cup\{k\})$: if that LP were unbounded, some variable $j\in J(\mathcal S)\cup J_k$ would have a zero column and $p_j>0$, which contradicts the existence of $x^{\mathcal S}$ (if $j\in J(\mathcal S)$) or of $\alpha^k$ (if $j\in J_k$).
--
--   Differences from the source:
--   - encoding: A non-negative integral matrix (Assumption 1) → a natural-number matrix cast to ℝ; reason: same instances
--   - reading: "Fix any S ∪ T and k ∈ S ∪ T", with x^S and α^k "the optimal solutions" → for all finite S, T, every k ∈ S ∪ T and every choice of optimal x^S and α^k; reason: the optimum need not be unique, and the statement holds for each choice
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, Lemma 4, p.41 (α^k from Lemma 3, display (29)); Assumption 1, p.23; standing assumption b > 0, p.40

import Mathlib
import Definitions.Def_CoverModular_Supplement_h
import Definitions.Def_CoverModular_Supplement_IsOptimalPrimal
import Definitions.Def_CoverModular_Supplement_alphaBar
import Definitions.Def_CoverModular_Supplement_IsOptimalAux

namespace CoverModular.Supplement

/-- **Lemma 4** (DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*,
SSRN 3844987, Appendix A.3, Lemma 4, p.41). Under Assumption 1 and the Appendix A.3 standing
assumption `b > 0`, fix `S, T ⊆ U` and `k ∈ S ∪ T`; let `x^S` be an optimal solution of (17) for
`A = S` and `α^k` an optimal solution of the auxiliary LP (29) for `k` built from `ᾱ^S`. Then
`∑_i b_i α^k_i + h(S) ≤ h(S ∪ {k})`.

**Formalization Note** `S ∪ {k}` is `insert k S`. The set `T` only locates `k`, as on the page.
No boundedness hypothesis is needed for `h(S ∪ {k})`: the existence of `x^S` and of `α^k`
excludes an unbounded LP (17) for `S ∪ {k}`. -/
theorem lemma_4 {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ) (p : Fin n → ℝ)
    (b : Fin m → ℝ) (J : U → Finset (Fin n)) (hp : ∀ j, 0 ≤ p j) (hb : ∀ i, 0 < b i)
    (S T : Finset U) (k : U) (hk : k ∈ S ∪ T) (xS : Fin n → ℝ)
    (hxS : IsOptimalPrimal a p b J S xS) (αk : Fin m → ℝ)
    (hαk : IsOptimalAux a p b J (alphaBar a p b xS) k αk) :
    ∑ i, b i * αk i + h a p b J S ≤ h a p b J (insert k S) := by sorry

end CoverModular.Supplement
