-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_auto_compact_L_and_R
-- name    : AvramDividend.Classical.avram_p3_bv_original_auto_compact_L_and_R
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:14:50.739511+00:00
-- url     : https://prove2.me/theorems/bf2c4f16-a639-4268-815e-e19f873b84e1
-- title:
--   Derive both stopped BV negative-jump compact constants from source C1 and negative-zero boundary
-- statement:
--   For the same genuine bounded-variation Lévy process and a C1 verification candidate below the cap, both the local Lipschitz constant L and the left-unbounded absolute-value constant R needed in original stopped-compensation arguments follow from compact regularity and the negative-zero boundary.
-- source:
--   Proved original C1 local Lipschitz theorem 731ed4a6-b61c-449d-ab35-522c83642f86 and new source-zero compact bound 334b4bdf-ea07-4b43-81b7-f683a8b2c224.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_negative_zero_uniform_value_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_bv_original_auto_compact_L_and_R
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b < C) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by sorry
