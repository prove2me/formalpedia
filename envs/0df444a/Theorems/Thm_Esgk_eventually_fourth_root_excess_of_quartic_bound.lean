-- Prove2me | Theorems.Thm_Esgk_eventually_fourth_root_excess_of_quartic_bound
-- name    : Esgk.eventually_fourth_root_excess_of_quartic_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-15T06:18:31.073197+00:00
-- url     : https://prove2.me/theorems/7d95bc08-375e-4121-a5fc-1d928968b2ea
-- title:
--   A quartic deficiency bound yields a fourth-root excess
-- statement:
--   For each natural number $n$, let $X_n$ be a family of objects, let $Q_n(x)$ be a predicate, and let $K_n(x)$ be an arbitrary natural-valued quantity. Suppose that there is a positive integer $A$ such that, for all sufficiently large $n$, every qualifying $x$ admits $\sigma\in\mathbb N$ satisfying
--
--   $$(n-1)+\sigma=3K_n(x),\qquad n\le A(\sigma+1)^4.$$
--
--   Then there are a real constant $c>0$ and a threshold after which every qualifying $x$ satisfies
--
--   $$K_n(x)\ge \frac n3+c n^{1/4}.$$
--
--   The constants are uniform over the family. In the geometric application, $x$ is an indexed planar configuration, $P=\operatorname{image}(x)$, and $Q_n(x)$ asserts injectivity and general position. The specialization is $K_n(x)=D(P)$, where $D(P)$ counts the distinct nonzero distances between points of $P$.
-- source:
--   Local Lean source: lean/Esgk/DeficiencyFourthRoot.lean, theorem Esgk.eventually_fourth_root_excess_of_quartic_bound. Mathematical source argument: Section 16, equations (16.7)–(16.9), of the Atomic proof of the ESGK n^(1/4) additive bound manuscript, revision 2026-09-14. This submission isolates the numerical abstraction and leaves the quartic geometric estimate as a hypothesis.

import Mathlib

set_option autoImplicit false

open Filter

namespace Esgk

theorem eventually_fourth_root_excess_of_quartic_bound
    {P : ℕ → Type} {Q : ∀ n, P n → Prop} {K : ∀ n, P n → ℕ}
    (hA : ∃ A : ℕ, 0 < A ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ p : P n, Q n p → ∃ σ : ℕ,
        (n - 1) + σ = 3 * K n p ∧ n ≤ A * (σ + 1) ^ 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ p : P n, Q n p →
      (n : ℝ) / 3 + c * (n : ℝ) ^ (1 / 4 : ℝ) ≤ K n p := by sorry

end Esgk
