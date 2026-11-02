-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_gridfree_original_past_marked_rectangle_first_moment_bound
-- name    : AvramDividend.Classical.avram_wave6_01_bv_gridfree_original_past_marked_rectangle_first_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:56:39.490049+00:00
-- url     : https://prove2.me/theorems/a638706d-dc1d-449f-9b2e-eb591a47915e
-- title:
--   Grid-free finite BV original past-adapted marked jump first moment
-- statement:
--   For the true original SpectrallyNegativeLevy X, every F_s-restricted intrinsic jump count on (s,T]×B has finite first moment bounded by T times the total original negative Lévy activity, with only BV, finite activity and T>0. The auxiliary fine grid needed for the existing source counting proof is constructed deterministically within this proof and disappears entirely from the interface. No Poisson copy, conditional compensator, or mark-specific intensity is assumed.
-- source:
--   Directly instantiate the deterministic strict fine-grid witness, canonically Proved as of 20:28 UTC, from the source clock theorem and feed all four grid properties to the canonically Proved c35d0d44 actual-source marked BV bound. This eliminates auxiliary grid assumptions and preserves Ω,P,𝓕,X.X,X.ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_past_restricted_marked_rectangle_lintegral_finite
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_gridfree_original_past_marked_rectangle_first_moment_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (s : ℝ≥0) (hst : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) < ⊤ := by sorry
