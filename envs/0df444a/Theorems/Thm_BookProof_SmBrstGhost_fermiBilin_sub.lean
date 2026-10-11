-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_sub
-- name    : BookProof.SmBrstGhost.fermiBilin_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:11:26.387309+00:00
-- url     : https://prove2.me/theorems/5f82c8af-d277-4fc7-96ec-e2372a9b2263
-- title:
--   `BookProof.SmBrstGhost.fermiBilin_sub` (M P : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin (M - P) : Module.End ℂ (FermiFock N)) = fermiBilin M - fermiBilin P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.fermiBilin_sub` (M P : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin (M - P) : Module.End ℂ (FermiFock N)) = fermiBilin M - fermiBilin P
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.fermiBilin_sub`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_sub
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

theorem BookProof.SmBrstGhost.fermiBilin_sub (M P : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (M - P) : Module.End ℂ (FermiFock N)) = fermiBilin M - fermiBilin P := by sorry
