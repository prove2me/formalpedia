-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_zero_drop_measurable
-- name    : AvramDividend.Classical.avram_locmoll_band_zero_drop_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:19:10.0264+00:00
-- url     : https://prove2.me/theorems/b5d9282a-f456-46df-ac7f-a9c84732bd8c
-- title:
--   The zero right-payment drop set is measurable
-- statement:
--   The zero right-payment drop set is measurable
-- source:
--   Exact atomic diffuse secant integral b980c2dc-b50f-4bb4-b148-7f7a2859258e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_zero_drop_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
    MeasurableSet U := by sorry
