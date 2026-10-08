-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_annih_mul_annih
-- name    : BookProof.SmBrstGhost.annih_mul_annih
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T12:59:35.495209+00:00
-- url     : https://prove2.me/theorems/adf2629a-12f3-41f7-aa71-50c73efbb91b
-- title:
--   `BookProof.SmBrstGhost.annih_mul_annih` {N : ℕ} (p q : Fin N) : (annih p : Module.End ℂ (FermiFock N)) * annih q = -(annih q * annih p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.annih_mul_annih` {N : ℕ} (p q : Fin N) : (annih p : Module.End ℂ (FermiFock N)) * annih q = -(annih q * annih p)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.annih_mul_annih`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.annih_mul_annih
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

theorem BookProof.SmBrstGhost.annih_mul_annih {N : ℕ} (p q : Fin N) :
    (annih p : Module.End ℂ (FermiFock N)) * annih q = -(annih q * annih p) := by sorry
