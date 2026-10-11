-- Prove2me | Theorems.Thm_BookProof_SmCar_fermiBilin_apply
-- name    : BookProof.SmCar.fermiBilin_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:22.553507+00:00
-- url     : https://prove2.me/theorems/aeeccab4-2147-402c-b5dd-14f138500a63
-- title:
--   `BookProof.SmCar.fermiBilin_apply` (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) : fermiBilin h ψ = ∑ i : Fin n, ∑ j : Fin n, h i j • creat i (annih j ψ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.fermiBilin_apply` (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) : fermiBilin h ψ = ∑ i : Fin n, ∑ j : Fin n, h i j • creat i (annih j ψ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.fermiBilin_apply`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.fermiBilin_apply
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.fermiBilin_apply (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) :
    fermiBilin h ψ = ∑ i : Fin n, ∑ j : Fin n, h i j • creat i (annih j ψ) := by sorry
