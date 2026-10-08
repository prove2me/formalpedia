-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_mul4
-- name    : BookProof.SmBrstGhost.fermiBilin_mul4
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T12:59:39.078093+00:00
-- url     : https://prove2.me/theorems/b43027da-8596-408a-8e08-25e83663b4fe
-- title:
--   `BookProof.SmBrstGhost.fermiBilin_mul4` (M P : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin M : Module.End ℂ (FermiFock N)) * fermiBilin P = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.fermiBilin_mul4` (M P : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin M : Module.End ℂ (FermiFock N)) * fermiBilin P = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, (M i j * P k l) • ((creat i * annih j) * (creat k * annih l))
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.fermiBilin_mul4`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_mul4
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

theorem BookProof.SmBrstGhost.fermiBilin_mul4 (M P : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin M : Module.End ℂ (FermiFock N)) * fermiBilin P
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
          (M i j * P k l) • ((creat i * annih j) * (creat k * annih l)) := by sorry
