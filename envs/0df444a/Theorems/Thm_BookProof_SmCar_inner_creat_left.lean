-- Prove2me | Theorems.Thm_BookProof_SmCar_inner_creat_left
-- name    : BookProof.SmCar.inner_creat_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:00:05.009993+00:00
-- url     : https://prove2.me/theorems/2d6dcbe7-c8d8-42f1-908e-91c48bcd0442
-- title:
--   `BookProof.SmCar.inner_creat_left` (i : Fin n) (ψ φ : FermiFock n) : (inner ℂ (creat i ψ) φ : ℂ) = inner ℂ ψ (annih i φ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.inner_creat_left` (i : Fin n) (ψ φ : FermiFock n) : (inner ℂ (creat i ψ) φ : ℂ) = inner ℂ ψ (annih i φ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.inner_creat_left`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.inner_creat_left
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.inner_creat_left (i : Fin n) (ψ φ : FermiFock n) :
    (inner ℂ (creat i ψ) φ : ℂ) = inner ℂ ψ (annih i φ) := by sorry
