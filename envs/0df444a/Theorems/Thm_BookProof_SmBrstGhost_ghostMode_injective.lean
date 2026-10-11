-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_ghostMode_injective
-- name    : BookProof.SmBrstGhost.ghostMode_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:08:01.333462+00:00
-- url     : https://prove2.me/theorems/e58327d3-38a2-4a4d-9854-9c3aa0cb01be
-- title:
--   `BookProof.SmBrstGhost.ghostMode_injective` (m : ℕ) : Function.Injective (ghostMode m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.ghostMode_injective` (m : ℕ) : Function.Injective (ghostMode m)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.ghostMode_injective`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.ghostMode_injective
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}

theorem BookProof.SmBrstGhost.ghostMode_injective (m : ℕ) : Function.Injective (ghostMode m) := by sorry
