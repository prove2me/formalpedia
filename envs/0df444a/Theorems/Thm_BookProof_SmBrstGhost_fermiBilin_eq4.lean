-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_eq4
-- name    : BookProof.SmBrstGhost.fermiBilin_eq4
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T12:59:39.161729+00:00
-- url     : https://prove2.me/theorems/1b830cb0-4722-447c-adb2-2456ebcd2fae
-- title:
--   `BookProof.SmBrstGhost.fermiBilin_eq4` (M : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin M : Module.End ℂ (FermiFock N)) = ∑ i : Fin N, ∑ j : Fin N, M i j • (creat i * annih j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.fermiBilin_eq4` (M : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin M : Module.End ℂ (FermiFock N)) = ∑ i : Fin N, ∑ j : Fin N, M i j • (creat i * annih j)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.fermiBilin_eq4`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_eq4
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.fermiBilin_eq4 (M : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin M : Module.End ℂ (FermiFock N))
      = ∑ i : Fin N, ∑ j : Fin N, M i j • (creat i * annih j) := by sorry
