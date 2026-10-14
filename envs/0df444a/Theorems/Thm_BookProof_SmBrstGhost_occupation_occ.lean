-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_occupation_occ
-- name    : BookProof.SmBrstGhost.occupation_occ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:08:26.921134+00:00
-- url     : https://prove2.me/theorems/2f6f20f4-f011-4147-878c-f7723a9e5864
-- title:
--   `BookProof.SmBrstGhost.occupation_occ` {N : ℕ} (i : Fin N) (S : Finset (Fin N)) : creat i (annih i (occ S)) = if i ∈ S then occ S else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.occupation_occ` {N : ℕ} (i : Fin N) (S : Finset (Fin N)) : creat i (annih i (occ S)) = if i ∈ S then occ S else 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.occupation_occ`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.occupation_occ
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

theorem BookProof.SmBrstGhost.occupation_occ {N : ℕ} (i : Fin N) (S : Finset (Fin N)) :
    creat i (annih i (occ S)) = if i ∈ S then occ S else 0 := by sorry
