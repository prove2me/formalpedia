-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
-- name    : AvramDividend.Classical.avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:38:13.526951+00:00
-- url     : https://prove2.me/theorems/d8a9025e-89a5-4a71-a9e9-d2dcca38a899
-- title:
--   Actual Lévy controlled predictable left reserve is jointly Borel measurable when zeroed after the finite source horizon
-- statement:
--   For the original Lévy process and original dividend strategy, the genuinely predictable strict-left-limit of the post-payment reserve, truncated to zero outside any finite physical time interval, is jointly measurable for the ambient Borel time × original sample probability sigma-algebra. This is a direct finite-clock integrand measurability bridge for any future intrinsic source-jump compensator; it is stronger than knowing only the strict interior event is measurable. No source replacement, mark Poisson copy, HJB smoothness, positive drift or jump compensation is assumed.
-- source:
--   Original controlled Lévy process, finite-horizon predictable jump and generator integrands in Avram-Palmowski-Pistorius (2007), Proposition 4(i). Imports only Proved 94ee9994 strongly predictable actual reserve. Uses finite rectangle strong progressiveness, ambient filtration monotonicity and measurable-set gluing with zero outside the horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × Ω =>
      if p.1 ≤ T then
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1
      else 0) := by sorry
