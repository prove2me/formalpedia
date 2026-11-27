-- Prove2me | Theorems.Thm_CoverModular_Supplement_theorem_2
-- name    : CoverModular.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:19:17.406948+00:00
-- url     : https://prove2.me/theorems/57b98593-f2f9-45be-838f-22586dac2123
-- title:
--   Theorem 2 (corrected: every LP (17) bounded) — the LP-based set function $h$ is nonnegative, monotone and $\bar a$-cover modular, and so is $h_{\mathbb Z}$ when $A$ is totally unimodular
-- statement:
--   Consider the LP-based subset selection problem (17). There are $n$ variables and $m$ constraints with data $p\in\mathbb R^n$, $A=[a_{ij}]$ and $b\in\mathbb R^m$, and a family $\{J_k\}_{k\in\mathcal U}$ of subsets of $\{1,\dots,n\}$. For $\mathcal A\subseteq\mathcal U$,
--
--   $$
--   h(\mathcal A)=\max_x\ \sum_jp_jx_j\quad\text{s.t.}\quad\sum_ja_{ij}x_j\le b_i\ (1\le i\le m),\qquad x_j=0\ (j\notin J(\mathcal A)),\qquad x\ge0,
--   $$
--
--   where $J(\mathcal A)=\bigcup_{k\in\mathcal A}J_k$. Let $h_{\mathbb Z}$ be the same program with the additional constraint $x\in\mathbb Z^n_+$, and let $\bar a=\max_j\sum_ia_{ij}$ be the column sparsity. Assume Assumption 1: $A$ is a non-negative integral matrix, and $p\ge0$, $b\ge0$. Assume also that every LP (17) is bounded above, so that $h$ is a real-valued set function. Then:
--
--   1. $h(\mathcal A)\ge0$ for every $\mathcal A$;
--   2. $h$ is monotone: $h(\mathcal A)\le h(\mathcal B)$ whenever $\mathcal A\subseteq\mathcal B$;
--   3. $h$ is $\bar a$-cover modular: for all $\mathcal S,\mathcal T\subseteq\mathcal U$,
--
--   $$
--   h(\mathcal S\cup\mathcal T)-\bar a\,h(\mathcal S)\le\sum_{k\in\mathcal T\setminus\mathcal S}\big(h(\mathcal S\cup\{k\})-h(\mathcal S)\big),
--   $$
--
--   and, when $\bar a\ge1$, $h$ is $\bar a$-cover modular in the sense of Definition 3;
--   4. if in addition $A$ is totally unimodular, items 1–3 hold with $h_{\mathbb Z}$ in place of $h$. Here $b$ need not be integral.
--
--   The theorem extends Theorem 1, the 2-cover modularity of the flexibility design objective, to any objective computed by a packing-type LP over a chosen set of variable groups. The cover modularity constant is the column sparsity of the constraint matrix. Through the greedy analysis of Proposition 3, it gives a $(1-(1-\bar a/K)^K)/\bar a$ approximation guarantee for the corresponding subset selection problems.
--
--   **Formalization Note** The boundedness hypothesis says that, for every finite $\mathcal A$, the objective values over the feasible set of (17) are bounded above. The maxima are written as suprema, which are the paper's maxima under this hypothesis. Integrality $x\in\mathbb Z^n_+$ is "every coordinate is an integer" together with $x\ge0$. Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular` of $A$ viewed as an integer matrix: every square submatrix has determinant $0$, $1$ or $-1$. The universe $\mathcal U$ is any type, and sets are finite subsets of it. The published Definition 3 (`CoverModular.IsCoverModular`) includes the range $\gamma\ge1$, so it is applied under $1\le\bar a$, and the inequality of item 3 is also stated on its own.
--
--   Differences from the source:
--   - correction: h defined in (17) is a real-valued set function under Assumption 1 → the hypothesis that every LP (17) is bounded above; reason: Assumption 1 does not make (17) bounded. With m = n = 1, a₁₁ = 0, p₁ = 1, b₁ = 1, J_k = {1}, Assumption 1 holds but the LP for {k} is unbounded, so h({k}) is not a real number and the claims are undefined. The hypothesis excludes exactly the instances where some h(A) = +∞
--   - generalization: h is ā-cover modular (Definition 3, which requires γ ≥ 1) → the inequality h(S ∪ T) − ā h(S) ≤ Σ_{k∈T∖S}(h(S ∪ {k}) − h(S)) for all S, T and every value of ā, plus IsCoverModular ā h when 1 ≤ ā; reason: the inequality also covers ā = 0 (zero matrix or m = 0), where Definition 3 does not apply, and for ā ≥ 1 it is exactly the source's claim
--   - encoding: A non-negative integral matrix → a natural-number matrix cast to ℝ (cast to ℤ for total unimodularity); reason: same instances
--   - encoding: x ∈ ℤⁿ₊ → real x ≥ 0 whose coordinates are integers; reason: same feasible points
--   - encoding: subsets S, T, A ⊆ U → finite sets Finset U; reason: the sum over T ∖ S in Definition 3 requires T ∖ S finite, and the paper's applications have a finite universe
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §5.1, Theorem 2, p.23 (Assumption 1, display (17), ā, p.23; Definition 3, p.9); proof in Appendix A.3, pp.40–44

import Mathlib
import Definitions.Def_CoverModular_IsCoverModular
import Definitions.Def_CoverModular_Supplement_h
import Definitions.Def_CoverModular_Supplement_hZ
import Definitions.Def_CoverModular_Supplement_colSparsity

namespace CoverModular.Supplement

/-- **Theorem 2** (DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*,
SSRN 3844987, §5.1, Theorem 2, p.23; proof in Appendix A.3, pp.40–44). Under Assumption 1
(`A = [a_ij]` non-negative integral, `p ≥ 0`, `b ≥ 0`), the LP-based set function `h` of (17) is
nonnegative, monotone and `ā`-cover modular, where `ā = max_j ∑_i a_ij` is the column sparsity:
`h(S ∪ T) − ā h(S) ≤ ∑_{k ∈ T \ S} (h(S ∪ {k}) − h(S))` for all `S, T`. If moreover `A` is
totally unimodular, the same holds for `h_Z`, the program (17) with `x ∈ ℤⁿ₊` added.

**Formalization Note** The paper treats `h` as a real-valued set function; the hypothesis `hbdd`
(every LP (17) is bounded above) states this. It excludes exactly the instances where some
`h(A)` is `+∞` (e.g. a zero column `j ∈ J_k` with `p_j > 0`), where Assumption 1 alone does not
make `h` real-valued. The cover-modular inequality is stated directly, so it also covers `ā = 0`
(zero matrix or `m = 0`), where Definition 3's range `γ ≥ 1` fails; the conjunct
`1 ≤ ā → IsCoverModular ā h` connects to the published Definition 3. Total unimodularity is
Mathlib's `Matrix.IsTotallyUnimodular` of the integer matrix; `b` need not be integral. -/
theorem theorem_2 {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ)
    (p : Fin n → ℝ) (b : Fin m → ℝ) (J : U → Finset (Fin n)) (hp : ∀ j, 0 ≤ p j)
    (hb : ∀ i, 0 ≤ b i)
    (hbdd : ∀ A : Finset U, BddAbove (objective p '' {x | Feasible a b J A x})) :
    ((∀ A : Finset U, 0 ≤ h a p b J A) ∧
      (∀ A B : Finset U, A ⊆ B → h a p b J A ≤ h a p b J B) ∧
      (∀ S T : Finset U, h a p b J (S ∪ T) - (colSparsity a : ℝ) * h a p b J S ≤
        ∑ k ∈ T \ S, (h a p b J (insert k S) - h a p b J S)) ∧
      ((1 : ℝ) ≤ colSparsity a → IsCoverModular (colSparsity a : ℝ) (h a p b J))) ∧
    ((Matrix.of fun i j => (a i j : ℤ)).IsTotallyUnimodular →
      (∀ A : Finset U, 0 ≤ hZ a p b J A) ∧
      (∀ A B : Finset U, A ⊆ B → hZ a p b J A ≤ hZ a p b J B) ∧
      (∀ S T : Finset U, hZ a p b J (S ∪ T) - (colSparsity a : ℝ) * hZ a p b J S ≤
        ∑ k ∈ T \ S, (hZ a p b J (insert k S) - hZ a p b J S)) ∧
      ((1 : ℝ) ≤ colSparsity a → IsCoverModular (colSparsity a : ℝ) (hZ a p b J))) := by sorry

end CoverModular.Supplement
