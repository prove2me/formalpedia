-- Prove2me | Theorems.Thm_BookProof_SmCar_smul_apply_fock
-- name    : BookProof.SmCar.smul_apply_fock
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:26:30.874986+00:00
-- url     : https://prove2.me/theorems/84c0691d-2656-40d2-ad8b-591a3d791db5
-- title:
--   `BookProof.SmCar.smul_apply_fock` (c : ℂ) (x : FermiFock n) (S : Finset (Fin n)) : (c • x) S = c * x S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.smul_apply_fock` (c : ℂ) (x : FermiFock n) (S : Finset (Fin n)) : (c • x) S = c * x S
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.smul_apply_fock`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.smul_apply_fock
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.smul_apply_fock (c : ℂ) (x : FermiFock n) (S : Finset (Fin n)) :
    (c • x) S = c * x S := by sorry
