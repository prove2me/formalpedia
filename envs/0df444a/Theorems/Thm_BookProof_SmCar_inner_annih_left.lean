-- Prove2me | Theorems.Thm_BookProof_SmCar_inner_annih_left
-- name    : BookProof.SmCar.inner_annih_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:27:28.012058+00:00
-- url     : https://prove2.me/theorems/624eb26b-d64c-43ec-a007-7a6d66a4b188
-- title:
--   `BookProof.SmCar.inner_annih_left` (i : Fin n) (ψ φ : FermiFock n) : (inner ℂ (annih i ψ) φ : ℂ) = inner ℂ ψ (creat i φ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.inner_annih_left` (i : Fin n) (ψ φ : FermiFock n) : (inner ℂ (annih i ψ) φ : ℂ) = inner ℂ ψ (creat i φ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.inner_annih_left`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.inner_annih_left
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.inner_annih_left (i : Fin n) (ψ φ : FermiFock n) :
    (inner ℂ (annih i ψ) φ : ℂ) = inner ℂ ψ (creat i φ) := by sorry
