-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_smul
-- name    : BookProof.SmBrstGhost.fermiBilin_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:10:05.191666+00:00
-- url     : https://prove2.me/theorems/0725004d-75fe-4aeb-b59e-0d5141d98aaa
-- title:
--   `BookProof.SmBrstGhost.fermiBilin_smul` (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin (c • M) : Module.End ℂ (FermiFock N)) = c • fermiBilin M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.fermiBilin_smul` (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin (c • M) : Module.End ℂ (FermiFock N)) = c • fermiBilin M
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.fermiBilin_smul`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_smul
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

theorem BookProof.SmBrstGhost.fermiBilin_smul (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (c • M) : Module.End ℂ (FermiFock N)) = c • fermiBilin M := by sorry
