-- Prove2me | Theorems.Thm_Erdos20_disjoint_of_bernoulli_hitting
-- name    : Erdos20.disjoint_of_bernoulli_hitting
-- status  : Proved
-- author  : @lunjia
-- created : 2026-09-26T16:17:21.476922+00:00
-- url     : https://prove2.me/theorems/1585ee7a-0fbf-44ed-9fd3-d8366b96dfea
-- title:
--   The BCW coloring step: one random petal yields many disjoint petals
-- statement:
--   Let $X$ be a finite ground set, let $\mathcal F$ be a finite family of nonempty subsets of $X$, and let $k\ge1$ be an integer. Include each element of $X$ independently in a random set $W$ with probability $p=1/(2k)$. If
--
--   $$\Pr(\exists A\in\mathcal F:\ A\subseteq W)\ge\tfrac12,$$
--
--   then there is a subfamily $\mathcal H\subseteq\mathcal F$ with
--
--   $$|\mathcal H|=k,\qquad A\cap B=\varnothing\quad\text{for all distinct }A,B\in\mathcal H.$$
--
--   This is the expectation-based coloring step in the Bell–Chueluecha–Warnke sunflower argument. It isolates the conversion from a single random-set containment estimate to several disjoint members. No spread or uniform-rank assumption is needed at this stage. Nonempty members are required so that members selected in different color classes are distinct.
--
--   **Formalization Note.** Sampling uses Mathlib's product Bernoulli measure on the entire finite ground type. The parameter is supplied as an element of the unit interval with its value explicitly specified.
-- source:
--   Bell, Chueluecha, Warnke, Note on Sunflowers, arXiv:2009.09327v2, proof of Lemma 2, final random-coloring/expectation argument, https://arxiv.org/html/2009.09327v2 . The generic implication here isolates that argument from the spread hypothesis.

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.NormNum
set_option autoImplicit false

namespace Erdos20
theorem disjoint_of_bernoulli_hitting {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.Nonempty)
    (k : ℕ) (hk : 0 < k) (p : unitInterval)
    (hp : (p : ℝ) = (2 * (k : ℝ))⁻¹)
    (hhit : (1 / 2 : ℝ) ≤
      (ProbabilityTheory.setBernoulli (Set.univ : Set α) p).real
        {W | ∃ A ∈ F, (A : Set α) ⊆ W}) :
    ∃ H ⊆ F, H.card = k ∧ ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by sorry
end Erdos20
