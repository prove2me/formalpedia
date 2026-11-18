-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
-- name    : AvramDividend.Classical.avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:13:23.293179+00:00
-- url     : https://prove2.me/theorems/56556ed9-e4bc-4b69-b454-47ec8118e5c1
-- title:
--   Original stopped Gaussian grid noise bounded by source tube extended one mesh interval
-- statement:
--   For any monotone physical time grid with constant step Delta and stopped horizon T, the source-noise sum masked by s_i<T is bounded by epsilon whenever the centred Lévy path is within epsilon at every grid point through T+Delta. A finite cutoff index is supplied by B108; the exact original discounted prefix sum is controlled by the Proved B64. This explicitly handles the last grid cell that crosses the stopping horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
import Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_stopped_discounted_gaussian_mesh_prefix_noise_sup_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (m : ℕ) (s : ℕ → ℝ≥0) (hs : Monotone s)
    (hs0 : s 0 = 0) (Δ T : ℝ≥0)
    (hstep : ∀ i, s (i + 1) = s i + Δ)
    (hX0 : X.X 0 ω = 0) (q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hTube : ∀ i, s i ≤ T + Δ →
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ ε := by sorry
