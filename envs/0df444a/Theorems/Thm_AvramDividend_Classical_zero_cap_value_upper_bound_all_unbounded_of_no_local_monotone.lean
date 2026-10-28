-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_no_local_monotone
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_no_local_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:42:07.323032+00:00
-- url     : https://prove2.me/theorems/2dec2ca9-439e-4e6a-af8e-9b8b80d1d6f3
-- title:
--   Global zero-cap dividend verification from nowhere-monotone initial Lévy paths
-- statement:
--   For a standing unbounded-variation spectrally negative Levy process, if almost every sample path fails to be monotone increasing on every interval beginning at zero, then the zero-barrier reflected ruin time is zero almost surely and the zero-barrier scale candidate bounds the optimal zero-capped dividend value at all nonnegative reserves. This pins down the missing unbounded-variation path-regularity input in a form directly linked to standard path-variation classification.
-- source:
--   No-local-monotone to instantaneous ruin theorem 4af9e9f0-e2fb-49c7-9723-e7ddb3b13696 (submitted), and canonically Proved global instant-ruin bound d7ea5cfe-8091-453c-ae72-62b42d5b18ca.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_no_local_monotone_path
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_no_local_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hNoMono : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
