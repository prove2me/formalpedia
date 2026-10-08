-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_creat_mul_creat
-- name    : BookProof.SmBrstGhost.creat_mul_creat
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T12:59:23.00786+00:00
-- url     : https://prove2.me/theorems/81197533-28f3-4bad-ac7c-6764f73d84ff
-- title:
--   `BookProof.SmBrstGhost.creat_mul_creat` {N : ℕ} (p q : Fin N) : (creat p : Module.End ℂ (FermiFock N)) * creat q = -(creat q * creat p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.creat_mul_creat` {N : ℕ} (p q : Fin N) : (creat p : Module.End ℂ (FermiFock N)) * creat q = -(creat q * creat p)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.creat_mul_creat`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.creat_mul_creat
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

theorem BookProof.SmBrstGhost.creat_mul_creat {N : ℕ} (p q : Fin N) :
    (creat p : Module.End ℂ (FermiFock N)) * creat q = -(creat q * creat p) := by sorry
