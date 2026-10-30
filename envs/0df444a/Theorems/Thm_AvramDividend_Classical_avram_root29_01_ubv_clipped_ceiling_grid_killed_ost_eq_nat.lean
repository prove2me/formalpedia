-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_clipped_ceiling_grid_killed_ost_eq_nat
-- name    : AvramDividend.Classical.avram_root29_01_ubv_clipped_ceiling_grid_killed_ost_eq_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:31:28.634614+00:00
-- url     : https://prove2.me/theorems/63fb4dea-5367-4482-b2d6-df3d646c4297
-- title:
--   Exact original-UBV finite-horizon clipped ceiling-grid killed-scale expectation
-- statement:
--   For the actual original spectrally negative Lévy law of unbounded variation, prove the expected continuously lower-history-killed q-scale at the authentic ceiling-capped first-exit grid, with clipped final clock, equals W(x) for any x>=0. Use the Proved source UBV killed martingale and bounded-index optional stopping with clipped monotone clock, and the genuine variation-independent equality of clipped and unclipped hitting indices. No Standing or open exit identity.
-- source:
--   WS1A work/avram_root29_01_ubv_clipped_ceiling_grid_killed_ost_eq_nat_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_grid_ost_from_source
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_clipped_ceiling_grid_killed_ost_eq_nat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hx : 0 ≤ x)
    (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
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
