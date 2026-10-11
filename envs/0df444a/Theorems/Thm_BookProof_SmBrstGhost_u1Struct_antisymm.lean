-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_u1Struct_antisymm
-- name    : BookProof.SmBrstGhost.u1Struct_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:07:31.019848+00:00
-- url     : https://prove2.me/theorems/77d4bb3a-f426-49d5-b9bd-29becfc9eb35
-- title:
--   `BookProof.SmBrstGhost.u1Struct_antisymm` (a b c : Fin 1) : u1Struct a b c = -u1Struct b a c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.u1Struct_antisymm` (a b c : Fin 1) : u1Struct a b c = -u1Struct b a c
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.u1Struct_antisymm`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.u1Struct_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.u1Struct_antisymm (a b c : Fin 1) : u1Struct a b c = -u1Struct b a c := by sorry
