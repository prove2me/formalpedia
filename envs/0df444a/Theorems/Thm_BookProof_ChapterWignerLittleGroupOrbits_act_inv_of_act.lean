-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_act_inv_of_act
-- name    : BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:54:49.479698+00:00
-- url     : https://prove2.me/theorems/b76d9629-4aea-42b2-9c46-c0de163b459c
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act` {A X Y : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (h : act A X = Y) : act A⁻¹ Y = X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act` {A X Y : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (h : act A X = Y) : act A⁻¹ Y = X
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act {A X Y : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (h : act A X = Y) :
    act A⁻¹ Y = X := by sorry
