-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_annih_sq
-- name    : BookProof.SmBrstGhost.annih_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T12:59:31.057982+00:00
-- url     : https://prove2.me/theorems/ff571df5-2206-414d-8fd5-35280d463328
-- title:
--   `BookProof.SmBrstGhost.annih_sq` {N : ℕ} (i : Fin N) : (annih i : Module.End ℂ (FermiFock N)) * annih i = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.annih_sq` {N : ℕ} (i : Fin N) : (annih i : Module.End ℂ (FermiFock N)) * annih i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.annih_sq`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.annih_sq
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

theorem BookProof.SmBrstGhost.annih_sq {N : ℕ} (i : Fin N) :
    (annih i : Module.End ℂ (FermiFock N)) * annih i = 0 := by sorry
