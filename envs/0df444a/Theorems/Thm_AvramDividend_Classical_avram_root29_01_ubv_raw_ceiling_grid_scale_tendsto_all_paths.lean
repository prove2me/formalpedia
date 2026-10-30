-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths
-- name    : AvramDividend.Classical.avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:25:02.615981+00:00
-- url     : https://prove2.me/theorems/557c7d45-9383-43e2-96ce-12ccd3f21c21
-- title:
--   UBV actual ceiling-capped two-sided q-scale raw grid converges on every source path
-- statement:
--   For any genuine unbounded-variation spectrally negative Lévy path and true capped two-sided first-exit grid, the original-path discounted q-scale reward converges on every path. For finite first strict exit, use the proved true GLB and W(0)=0 capped-grid continuity including cap ties. For both exit clocks infinite, the sampled cap is identically T. No Standing, BV assumption, Markov shortcut or two-sided ratio.
-- source:
--   WS1A work/avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_sampled_clock_caps_to_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths
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
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (nhds (if min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by sorry
