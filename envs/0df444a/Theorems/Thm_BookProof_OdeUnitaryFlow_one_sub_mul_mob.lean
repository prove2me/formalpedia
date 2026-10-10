-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_one_sub_mul_mob
-- name    : BookProof.OdeUnitaryFlow.one_sub_mul_mob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:42.437141+00:00
-- url     : https://prove2.me/theorems/cdb1c19c-5533-4cbb-98d6-f230456a77c4
-- title:
--   `BookProof.OdeUnitaryFlow.one_sub_mul_mob` (t x : ℝ) (hx : x ∈ flowDom t) : 1 - t * mob t x = (1 + t * x)⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.one_sub_mul_mob` (t x : ℝ) (hx : x ∈ flowDom t) : 1 - t * mob t x = (1 + t * x)⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.one_sub_mul_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.one_sub_mul_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.one_sub_mul_mob (t x : ℝ) (hx : x ∈ flowDom t) :
    1 - t * mob t x = (1 + t * x)⁻¹ := by sorry
