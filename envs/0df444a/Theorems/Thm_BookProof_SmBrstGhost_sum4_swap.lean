-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_sum4_swap
-- name    : BookProof.SmBrstGhost.sum4_swap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:09:38.662601+00:00
-- url     : https://prove2.me/theorems/73e9e5b4-1a2f-4b0c-bad0-2c14ae3766e6
-- title:
--   `BookProof.SmBrstGhost.sum4_swap` (F : Fin N → Fin N → Fin N → Fin N → Module.End ℂ (FermiFock N)) : ∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, F i j k l = ∑ i : Fin...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.sum4_swap` (F : Fin N → Fin N → Fin N → Fin N → Module.End ℂ (FermiFock N)) : ∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, F i j k l = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, F i j k l
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.sum4_swap`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.sum4_swap
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.sum4_swap (F : Fin N → Fin N → Fin N → Fin N → Module.End ℂ (FermiFock N)) :
    ∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, F i j k l
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, F i j k l := by sorry
