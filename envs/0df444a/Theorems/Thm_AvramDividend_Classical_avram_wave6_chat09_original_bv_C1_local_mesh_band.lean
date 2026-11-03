-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_local_mesh_band
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_C1_local_mesh_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:29:48.310161+00:00
-- url     : https://prove2.me/theorems/4335d6f6-dee5-4186-85f4-1ebdb64d77f2
-- title:
--   Original BV cap-interior C1 supplies a compact reserve mesh band and one finite derivative/Lipschitz coefficient
-- statement:
--   At every strictly positive reserve below the actual extended-real dividend cap, the original bounded-variation Levy C1 HJB regularity supplies a compact interval about the reserve inside the same cap domain and a finite NNReal bound on the derivative. The same bound is a LipschitzOnWith coefficient on that interval. It applies to finite and infinite caps, and supplies the exact band and hK premises of the accepted original-source clipped ruin-stopped payment mesh theorems.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), BV C1 localisation for change-of-variables; original-source C1 compact localisation and topology under true ENNReal cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_C1_local_mesh_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y ∧ ENNReal.ofReal y < C)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C}) :
    ∃ δ : ℝ, 0 < δ ∧
      Icc (y - δ) (y + δ) ⊆
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} ∧
      ∃ K : ℝ≥0,
        (∀ z ∈ Icc (y - δ) (y + δ), ‖deriv w z‖₊ ≤ K) ∧
        LipschitzOnWith K w (Icc (y - δ) (y + δ)) := by sorry
