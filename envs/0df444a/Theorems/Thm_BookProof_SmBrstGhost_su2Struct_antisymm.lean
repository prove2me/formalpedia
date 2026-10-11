-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_su2Struct_antisymm
-- name    : BookProof.SmBrstGhost.su2Struct_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:07:11.639462+00:00
-- url     : https://prove2.me/theorems/55c357aa-891c-4ff2-8baa-2318a24a2a9d
-- title:
--   `BookProof.SmBrstGhost.su2Struct_antisymm` (a b c : Fin 3) : su2Struct a b c = -su2Struct b a c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.su2Struct_antisymm` (a b c : Fin 3) : su2Struct a b c = -su2Struct b a c
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.su2Struct_antisymm`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.su2Struct_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.su2Struct_antisymm (a b c : Fin 3) : su2Struct a b c = -su2Struct b a c := by sorry
