-- Prove2me | Theorems.Thm_BookProof_SmCar_fermiBilin_symmetric
-- name    : BookProof.SmCar.fermiBilin_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:31:50.168456+00:00
-- url     : https://prove2.me/theorems/f4117f1c-1256-49bd-afe1-1ee81861b828
-- title:
--   `BookProof.SmCar.fermiBilin_symmetric` {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.conjTranspose = h) (ψ φ : FermiFock n) : (inner ℂ (fermiBilin h ψ) φ : ℂ) = inner ℂ ψ (fermiBilin h φ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.fermiBilin_symmetric` {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.conjTranspose = h) (ψ φ : FermiFock n) : (inner ℂ (fermiBilin h ψ) φ : ℂ) = inner ℂ ψ (fermiBilin h φ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.fermiBilin_symmetric`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.fermiBilin_symmetric
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.fermiBilin_symmetric {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.conjTranspose = h)
    (ψ φ : FermiFock n) :
    (inner ℂ (fermiBilin h ψ) φ : ℂ) = inner ℂ ψ (fermiBilin h φ) := by sorry
