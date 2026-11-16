-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq_nat_index
-- name    : AvramDividend.Classical.avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq_nat_index
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T15:28:19.8102+00:00
-- url     : https://prove2.me/theorems/0b88775b-5cd8-447d-81a5-e647600440a9
-- title:
--   Authentic original BV clipped uniform Nat grid scale-function optional stopping
-- statement:
--   Explicitly Nat-indexed clipped grid killed-scale optional stopping: K is a Nat-valued discrete first exit index, with hK an equality between Nat hitting indices of the actual original Lévy grid. The unannotated prior theorem elaborates hK instead as a continuous NNReal-indexed hitting time, leading to a type mismatch; this theorem fixes the hypothesis to its intended genuine discrete grid.
-- source:
--   Corrected Nat-indexed formulation of 156dee38 and Proved Avram ws01b killed-scale discrete optional stopping

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_grid_optional_stopping
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq_nat_index
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hx : 0 ≤ x) (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
    (K : Ω → ℕ)
    (hK : ∀ η, K η = hittingBtwn
      (fun (k : ℕ) ξ => max (X.X ((k : ℝ≥0) * δ) ξ - (a-x))
        ((-x) - X.X ((k : ℝ≥0) * δ) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / δ)) η) :
    (∫ ω,
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K η : ℝ≥0) * δ) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min ((K η : ℝ≥0) * δ) T) : ℝ))) *
          W (x + X.X (min ((K η : ℝ≥0) * δ) T) η)) ω ∂P) = W x := by sorry
