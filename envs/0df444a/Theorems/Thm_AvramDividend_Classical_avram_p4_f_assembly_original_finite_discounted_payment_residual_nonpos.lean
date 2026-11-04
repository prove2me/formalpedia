-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_discounted_payment_residual_nonpos
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_discounted_payment_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:23:44.460295+00:00
-- url     : https://prove2.me/theorems/5ce0a134-044d-47ed-91dc-b25458e55590
-- title:
--   Every finite family of true discounted original payments has a nonpositive value-loss residual
-- statement:
--   The canonical original-process jump admissibility inequality sums over every finite subset of actual eligible payment times, giving the finite-sum nonpositivity of discounted dividend-minus-value-loss residuals. This is the finite-approximation ingredient for the countable original Cash atom martingale budget.
-- source:
--   Original P4-F canonical 0dda1be7, genuine rightLimit payments and riskProcess values; finite Finset sum monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_discounted_payment_residual_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (helig : ∀ t ∈ S,
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ S, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))))) ≤ 0 := by sorry
