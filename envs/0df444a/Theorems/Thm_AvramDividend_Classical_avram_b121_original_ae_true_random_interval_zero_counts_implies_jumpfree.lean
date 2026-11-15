-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b121_original_ae_true_random_interval_zero_counts_implies_jumpfree
-- name    : AvramDividend.Classical.avram_b121_original_ae_true_random_interval_zero_counts_implies_jumpfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:26:45.073203+00:00
-- url     : https://prove2.me/theorems/c5ae87a0-e339-4e6c-8790-a2bc557e2313
-- title:
--   True original random stopped intervals are physically jumpfree on a conull event whenever every negative-mark Poisson cutoff count vanishes there
-- statement:
--   For genuinely random original source stopped endpoints s(omega),t(omega), suppose their order holds pathwise and all original negative-mark Poisson cutoff counts in the exact physical half-open stopped interval vanish on a single conull event simultaneously over all cutoff indices. On that same event the proved physical B112 count-to-jumpfree bridge gives zero actual original source jump at every time in the stopped interval. This avoids strengthening the original almost-everywhere Poisson/source convergence to all paths and discharges the true random-clock hNoJump premise needed by the compensated small and large mark source identities.
-- source:
--   Prepared direct original B125 theorem and canonical restricted a.e. filter_upwards transfer; publication awaits B125 Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the genuine source conull event with empty all-negative Poisson bands at the stopped random clocks, the same physical interval is truly jumpfree. -/

theorem AvramDividend.Classical.avram_b121_original_ae_true_random_interval_zero_counts_implies_jumpfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : Ω → ℝ≥0) (hst : ∀ ω, s ω ≤ t ω)
    (hZero : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s ω) (t ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by sorry
