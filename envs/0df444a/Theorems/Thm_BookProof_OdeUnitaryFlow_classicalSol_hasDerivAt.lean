-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_classicalSol_hasDerivAt
-- name    : BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:40:37.352389+00:00
-- url     : https://prove2.me/theorems/b7ab945c-1374-430a-b15b-0bb9748fa60b
-- title:
--   `BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt` (x₀ t : ℝ) (ht : 1 - t * x₀ ≠ 0) : HasDerivAt (classicalSol x₀) ((classicalSol x₀ t) ^ 2) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt` (x₀ t : ℝ) (ht : 1 - t * x₀ ≠ 0) : HasDerivAt (classicalSol x₀) ((classicalSol x₀ t) ^ 2) t
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt (x₀ t : ℝ) (ht : 1 - t * x₀ ≠ 0) :
    HasDerivAt (classicalSol x₀) ((classicalSol x₀ t) ^ 2) t := by sorry
