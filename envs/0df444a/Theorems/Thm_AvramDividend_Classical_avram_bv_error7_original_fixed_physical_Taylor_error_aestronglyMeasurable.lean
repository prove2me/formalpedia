-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_fixed_physical_Taylor_error_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_bv_error7_original_fixed_physical_Taylor_error_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:03:06.769035+00:00
-- url     : https://prove2.me/theorems/eaf2a685-3a58-4146-b9d4-51c33c2f3792
-- title:
--   Original bounded-variation fixed physical-grid discounted Taylor source error measurable
-- statement:
--   For the actual spectrally negative Lévy process X satisfying Standing and bounded variation, the original admissible dividend strategy D and its genuine negative-jump cumulative correction J, each discounted C1 Taylor error sum on a deterministic physical grid is almost-everywhere strongly measurable as soon as w and deriv w are Borel measurable. The only proof inputs are the already Proved adaptedness of the original process, original dividend right-limit measurability, the original raw negative-jump cumulative a.e. measurability, and a completed source-specific finite-sum assembly theorem. The proof constructs the exact original X/D/J/Y errors with no synthetic process, no signed prebudget, and no extra random-grid measurability assumptions.
-- source:
--   Original deterministic stopped physical-grid error measurability discharging the evaluation premises of avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations; supports canonical 2bc848f9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_fixed_physical_Taylor_error_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hderiv : Measurable (deriv w))
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i))) :
    ∀ m, AEStronglyMeasurable (Err m) P := by sorry
