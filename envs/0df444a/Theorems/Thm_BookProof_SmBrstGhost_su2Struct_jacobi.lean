-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_su2Struct_jacobi
-- name    : BookProof.SmBrstGhost.su2Struct_jacobi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:07:10.098004+00:00
-- url     : https://prove2.me/theorems/385b0686-d696-4eff-a4ac-5121a75a1b40
-- title:
--   `BookProof.SmBrstGhost.su2Struct_jacobi` (a b c h : Fin 3) : ∑ e, (su2Struct a b e * su2Struct e c h + su2Struct b c e * su2Struct e a h + su2Struct c a e * su2Struct e b h) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.su2Struct_jacobi` (a b c h : Fin 3) : ∑ e, (su2Struct a b e * su2Struct e c h + su2Struct b c e * su2Struct e a h + su2Struct c a e * su2Struct e b h) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.su2Struct_jacobi`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.su2Struct_jacobi
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.su2Struct_jacobi (a b c h : Fin 3) :
    ∑ e, (su2Struct a b e * su2Struct e c h + su2Struct b c e * su2Struct e a h
      + su2Struct c a e * su2Struct e b h) = 0 := by sorry
