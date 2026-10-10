-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_hasDerivAt_mob
-- name    : BookProof.OdeUnitaryFlow.hasDerivAt_mob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:48.99618+00:00
-- url     : https://prove2.me/theorems/be46d18a-eec3-4a94-87ab-c655316e4553
-- title:
--   `BookProof.OdeUnitaryFlow.hasDerivAt_mob` (t x : ℝ) (hx : x ∈ flowDom t) : HasDerivAt (mob t) ((1 + t * x) ^ 2)⁻¹ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.hasDerivAt_mob` (t x : ℝ) (hx : x ∈ flowDom t) : HasDerivAt (mob t) ((1 + t * x) ^ 2)⁻¹ x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.hasDerivAt_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.hasDerivAt_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.hasDerivAt_mob (t x : ℝ) (hx : x ∈ flowDom t) :
    HasDerivAt (mob t) ((1 + t * x) ^ 2)⁻¹ x := by sorry
