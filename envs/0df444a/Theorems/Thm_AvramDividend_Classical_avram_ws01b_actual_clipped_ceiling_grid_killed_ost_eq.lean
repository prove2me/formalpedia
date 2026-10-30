-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq
-- name    : AvramDividend.Classical.avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-10-29T12:52:40.994692+00:00
-- url     : https://prove2.me/theorems/156dee38-2fe2-414f-aba5-6eee56301f5d
-- title:
--   Exact finite-horizon original BV history-killed q-scale expectation at the actual ceiling stopped grid
-- statement:
--   For any positive mesh and finite horizon, take the genuine bounded two-sided first-crossing index observed at the original Lévy grid times, clip the selected clock at the horizon, and kill discounted terminal q-scale reward on any historically negative reserve. Its true expectation equals Wq(x) under Standing and bounded variation. The source equality is obtained via the accepted pathwise equivalence between unclipped and capped crossing indices and the genuine killed discrete optional-stopping identity.
-- source:
--   Accepted BV original-law killed grid optional stopping e7f81c41, monotonic clipped clock and genuine clipped/unclipped hittingBtwn congruence. Exact original source clock, reward and survival event.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_grid_optional_stopping
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hx : 0 ≤ x) (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
    (K : Ω → ℕ)
    (hK : ∀ η, K η = hittingBtwn
      (fun k ξ => max (X.X ((k : ℝ≥0) * δ) ξ - (a-x))
        ((-x) - X.X ((k : ℝ≥0) * δ) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / δ)) η) :
    (∫ ω,
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K η : ℝ≥0) * δ) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min ((K η : ℝ≥0) * δ) T) : ℝ))) *
          W (x + X.X (min ((K η : ℝ≥0) * δ) T) η)) ω ∂P) = W x := by sorry
