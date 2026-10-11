-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_add_prime
-- name    : BookProof.SmBrstGhost.fermiBilin_add_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:10:10.479974+00:00
-- url     : https://prove2.me/theorems/41186d92-4d27-4e80-890c-ae5e5d3b9462
-- title:
--   BookProof.SmBrstGhost.fermiBilin_add'
-- statement:
--   BookProof.SmBrstGhost.fermiBilin_add'

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_add'
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.fermiBilin_add_prime (M P : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (M + P) : Module.End ℂ (FermiFock N)) = fermiBilin M + fermiBilin P := by sorry
