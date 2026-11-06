-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_finite_tagged_nonlinear_comparison
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_finite_tagged_nonlinear_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:24:44.873195+00:00
-- url     : https://prove2.me/theorems/dd78959c-f803-47db-9c78-507ea84e4f76
-- title:
--   Physical-grid original BV nonlinear jump sum compared to tagged actual jump sum with discount mismatch
-- statement:
--   For an arbitrary finite physical mesh, compare discounted aggregate negative Lévy jump nonlinear terms with the same nonlinear terms evaluated at original tagged jump prestates and their actual jump-time discounts. Under a finite compact Lipschitz bound and nonnegative physical-grid discount weights, the total discrepancy is bounded by residual unmarked negative-jump mass, twice the prestate approximation error and a separate exact jump-time discount mismatch. This distinct two-weight estimate is the finite-tagged pathwise step needed to combine F2 physical cell convergence with the literal original marked jump counting integral. The Lipschitz premise must later be instantiated only on valid compact interior ranges; the theorem itself makes no global assertion about the dividend candidate.
-- source:
--   Finite BV physical-jump cell decomposition and weighted finite-sum triangle. Uses the exact physical-grid variables from Proved F2 original tagged source remainder 59bbb211 and original source cash/grid 317d835e.

import Mathlib

open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_finite_tagged_nonlinear_comparison
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, |w x - w y| ≤ L * |x - y|)
    (n : ℕ) (e d z p j a : Fin n → ℝ)
    (he : ∀ i, 0 ≤ e i) :
    |(∑ i : Fin n, e i * (w (z i - j i) - w (z i))) -
      (∑ i : Fin n, d i * (w (p i - a i) - w (p i)))| ≤
      (∑ i : Fin n, e i *
        (L * |j i - a i| + 2 * L * |z i - p i|)) +
      (∑ i : Fin n, |e i - d i| *
        |w (p i - a i) - w (p i)|) := by sorry
