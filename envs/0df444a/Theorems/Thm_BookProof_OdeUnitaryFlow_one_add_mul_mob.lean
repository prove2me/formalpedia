-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_one_add_mul_mob
-- name    : BookProof.OdeUnitaryFlow.one_add_mul_mob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:56.998402+00:00
-- url     : https://prove2.me/theorems/df3c6c96-bec7-4a74-929d-162a5732e5e4
-- title:
--   `BookProof.OdeUnitaryFlow.one_add_mul_mob` (s t x : ℝ) (hx : 1 + t * x ≠ 0) : 1 + s * mob t x = (1 + (s + t) * x) / (1 + t * x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.one_add_mul_mob` (s t x : ℝ) (hx : 1 + t * x ≠ 0) : 1 + s * mob t x = (1 + (s + t) * x) / (1 + t * x)
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.one_add_mul_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.one_add_mul_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.one_add_mul_mob (s t x : ℝ) (hx : 1 + t * x ≠ 0) :
    1 + s * mob t x = (1 + (s + t) * x) / (1 + t * x) := by sorry
