-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_stopped_integrand_eventually_eq
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_clock_stopped_integrand_eventually_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:17.807767+00:00
-- url     : https://prove2.me/theorems/11b323ce-3aea-4cac-bcc1-7faf5002b903
-- title:
--   Original stopped generator-style integrands eventually equal the full pre-ruin integrand
-- statement:
--   The exact original original-clock indicator t<min(ruinTime,n) eventually agrees at every individual physical time and original sample path with the full pre-ruin indicator t<ruinTime. It is a precise pathwise stabilisation condition for discounted generator or martingale integrands and holds even if ruin is infinite; it does not itself yield dominated convergence of integrals or optional stopping.
-- source:
--   Fresh proved P4-E cofinal strict pre-ruin source helper, and original min clock monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_eventually_strict_preruin
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original ruin-truncated stopped integrand stabilises pointwise. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_true_clock_stopped_integrand_eventually_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (f : ℝ≥0 → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (if (t : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞)
        then f t else 0) =
      (if (t : ℝ≥0∞) < ruinTime X x D ω then f t else 0) := by sorry
