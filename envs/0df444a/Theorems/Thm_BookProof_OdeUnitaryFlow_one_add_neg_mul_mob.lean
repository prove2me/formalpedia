-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_one_add_neg_mul_mob
-- name    : BookProof.OdeUnitaryFlow.one_add_neg_mul_mob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:23.73244+00:00
-- url     : https://prove2.me/theorems/d9bf79b3-0f3e-40b4-92ba-eb5177f0fa4f
-- title:
--   `BookProof.OdeUnitaryFlow.one_add_neg_mul_mob` (t x : ℝ) (hx : x ∈ flowDom t) : 1 + (-t) * mob t x = (1 + t * x)⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.one_add_neg_mul_mob` (t x : ℝ) (hx : x ∈ flowDom t) : 1 + (-t) * mob t x = (1 + t * x)⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.one_add_neg_mul_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.one_add_neg_mul_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.one_add_neg_mul_mob (t x : ℝ) (hx : x ∈ flowDom t) :
    1 + (-t) * mob t x = (1 + t * x)⁻¹ := by sorry
