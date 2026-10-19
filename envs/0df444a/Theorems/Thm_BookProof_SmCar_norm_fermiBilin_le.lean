-- Prove2me | Theorems.Thm_BookProof_SmCar_norm_fermiBilin_le
-- name    : BookProof.SmCar.norm_fermiBilin_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:27:43.196504+00:00
-- url     : https://prove2.me/theorems/a88bf9f5-7847-4671-8e29-53d231e387c2
-- title:
--   `BookProof.SmCar.norm_fermiBilin_le` (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) : ‖fermiBilin h ψ‖ ≤ (∑ i : Fin n, ∑ j : Fin n, ‖h i j‖) * ‖ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.norm_fermiBilin_le` (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) : ‖fermiBilin h ψ‖ ≤ (∑ i : Fin n, ∑ j : Fin n, ‖h i j‖) * ‖ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.norm_fermiBilin_le`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.norm_fermiBilin_le
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.norm_fermiBilin_le (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) :
    ‖fermiBilin h ψ‖ ≤ (∑ i : Fin n, ∑ j : Fin n, ‖h i j‖) * ‖ψ‖ := by sorry
