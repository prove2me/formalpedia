-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
-- name    : AvramDividend.Classical.avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:00:59.55022+00:00
-- url     : https://prove2.me/theorems/275ec0d1-ccbd-4605-bd92-00221ae5847f
-- title:
--   Actual original BV finite-activity physical negative jump counting measure has zero mass on the true final uniform horizon strip eventually almost surely
-- statement:
--   On a single conull event, the true original spectrally negative bounded variation finite negative activity Levy jump counting measure assigns zero source mass to each prescribed original final open-left terminal cell beyond the strict grid endpoint for all sufficiently large n. This is the exact count-measure version of Proved BVB45. The original source process, source leftLimit, original filtered probability space, original physical grid, actual terminal horizon and full counting support remain unchanged. It helps justify that eventual actual compensator-versus-jump differences across the terminal strip arise only from the predictable intensity, not physical jumps.
-- source:
--   Accepted original terminal physical jump exclusion b7ae7c05 and Mathlib Measure.count.restrict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual original source negative-jump counting measure assigns zero
mass to the prescribed terminal uniform-grid strip eventually a.s. -/

theorem AvramDividend.Classical.avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0})
        (Ioc (u n (n + 1)) S) = 0 := by sorry
