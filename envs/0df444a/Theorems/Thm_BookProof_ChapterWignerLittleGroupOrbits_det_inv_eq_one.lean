-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_det_inv_eq_one
-- name    : BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:54:29.57213+00:00
-- url     : https://prove2.me/theorems/9a5fa1e4-314b-4fbd-9c00-7c2dbbae31f9
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) : (A⁻¹).det = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) : (A⁻¹).det = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one
import Definitions.Def_ChapterWignerLittleGroup
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) : (A⁻¹).det = 1 := by sorry
