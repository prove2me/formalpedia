-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_fermiBilin_add
-- name    : BookProof.SmDiracYukawa.fermiBilin_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:32:13.272321+00:00
-- url     : https://prove2.me/theorems/42ce67fe-06aa-486b-bb9b-86825da40510
-- title:
--   `BookProof.SmDiracYukawa.fermiBilin_add` (A B : Matrix (Fin n) (Fin n) ℂ) : fermiBilin (A + B) = fermiBilin A + fermiBilin B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.fermiBilin_add` (A B : Matrix (Fin n) (Fin n) ℂ) : fermiBilin (A + B) = fermiBilin A + fermiBilin B
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.fermiBilin_add`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.fermiBilin_add
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.fermiBilin_add (A B : Matrix (Fin n) (Fin n) ℂ) :
    fermiBilin (A + B) = fermiBilin A + fermiBilin B := by sorry
