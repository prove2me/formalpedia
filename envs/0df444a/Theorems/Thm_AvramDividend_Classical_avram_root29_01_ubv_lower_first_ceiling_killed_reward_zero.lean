-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_lower_first_ceiling_killed_reward_zero
-- name    : AvramDividend.Classical.avram_root29_01_ubv_lower_first_ceiling_killed_reward_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:18:33.435994+00:00
-- url     : https://prove2.me/theorems/6106e5b4-7b25-4bd1-8a15-a62effd502d3
-- title:
--   Actual UBV lower-first continuously killed ceiling-grid q-scale reward vanishes
-- statement:
--   For a genuine original spectrally negative Lévy path of unbounded variation with strict lower-first exit by cap T, prove the exact full-history-killed clipped ceiling-grid q-scale reward converges to zero. The terminal reserve is at or below the lower barrier by the accepted true first-downcrossing theorem; the true UBV scale vanishes both below zero and at zero. Apply the accepted actual uncapped/ceiling raw first-exit convergence, then sandwich the killed reward by zero and the unrestricted positive reward, including lower creeping and terminal tie without Standing or any Open exit ratio.
-- source:
--   WS1A work/avram_root29_01_ubv_lower_first_ceiling_killed_reward_zero_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_lower_first_ceiling_killed_reward_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (nhds 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (hDown : twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a-x) ω)
    (hCap : (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min
            ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
      atTop (nhds 0) := by sorry
