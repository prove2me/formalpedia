-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_annih_mul_creat
-- name    : BookProof.SmBrstGhost.annih_mul_creat
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T12:59:09.196266+00:00
-- url     : https://prove2.me/theorems/b1709907-c213-47a7-b1d2-21433f58f0c4
-- title:
--   `BookProof.SmBrstGhost.annih_mul_creat` {N : ℕ} (p q : Fin N) : (annih p : Module.End ℂ (FermiFock N)) * creat q = (if p = q then 1 else 0) - creat q * annih p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.annih_mul_creat` {N : ℕ} (p q : Fin N) : (annih p : Module.End ℂ (FermiFock N)) * creat q = (if p = q then 1 else 0) - creat q * annih p
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.annih_mul_creat`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.annih_mul_creat
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

theorem BookProof.SmBrstGhost.annih_mul_creat {N : ℕ} (p q : Fin N) :
    (annih p : Module.End ℂ (FermiFock N)) * creat q
      = (if p = q then 1 else 0) - creat q * annih p := by sorry
