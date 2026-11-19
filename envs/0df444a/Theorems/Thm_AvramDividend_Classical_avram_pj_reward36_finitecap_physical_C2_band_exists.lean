-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward36_finitecap_physical_C2_band_exists
-- name    : AvramDividend.Classical.avram_pj_reward36_finitecap_physical_C2_band_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:58:25.427208+00:00
-- url     : https://prove2.me/theorems/58184d4f-5eda-4d6b-9be9-6e0c346e282b
-- title:
--   Finite-cap smooth original pure-jump source has nondegenerate compact interior Ito band
-- statement:
--   A finite strictly positive dividend cap and C2 candidate w on its physical open interior admit an actual positive compact band 0<u,u+delta<v<Cband with v<cap, delta in (0,1], with C2 regularity on (0,Cband). This is the geometric witness in the original physical Ito/Stieltjes positive residual source33; the signed source limit is a separate obligation.
-- source:
--   Mathlib ENNReal.toReal_pos and ofReal_lt_iff_lt_toReal, compact interior band construction used by the original stopped purejump source 2b5b6724.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward36_finitecap_physical_C2_band_exists
    (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ Cband u v δ : ℝ,
      0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧
      v < Cband ∧ v < C.toReal ∧
      ContDiffOn ℝ 2 w (Ioo 0 Cband) := by sorry
