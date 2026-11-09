-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_nonzero_jump_strictly_negative
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_nonzero_jump_strictly_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:33:22.070573+00:00
-- url     : https://prove2.me/theorems/2ba2b75a-b46d-4afe-b863-4fd40e189d2c
-- title:
--   Every nonzero source Lévy jump is strictly negative
-- statement:
--   For every sample path of the original source Lévy process, the actual jump X_u minus its left limit at any strictly positive time is strictly negative whenever it is nonzero. The proof derives the left limit using the source leftLim field and applies the pathwise noPosJumps source field; no measure-rate assumptions are needed.
-- source:
--   Original SpectrallyNegativeLevy definition 933ced80, fields leftLim and noPosJumps; pinned Mathlib leftLim_eq_of_tendsto and nhdsLT_neBot_of_exists_lt.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_nonzero_jump_strictly_negative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (hu : 0 < u)
    (hjump : X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 := by sorry
