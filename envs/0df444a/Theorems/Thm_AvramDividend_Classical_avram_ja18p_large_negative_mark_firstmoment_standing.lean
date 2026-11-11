-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p_large_negative_mark_firstmoment_standing
-- name    : AvramDividend.Classical.avram_ja18p_large_negative_mark_firstmoment_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:46:55.848147+00:00
-- url     : https://prove2.me/theorems/887ac2d6-39f7-461f-94ae-5c4be576fc89
-- title:
--   Standing integrability implies finite first absolute moment of original large-negative Lévy marks
-- statement:
--   For the actual process X with integrable X_1 in Standing, show ∫_{(-∞,-1]} |z| ν(dz)<∞. No assumption on small-jump first moments.
-- source:
--   AVRAM J-A18 original zero-cutoff Gaussian martingale integrability, 70393ec7 via 37d22393; all on same X and P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p_large_negative_mark_firstmoment_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) < ⊤ := by sorry
