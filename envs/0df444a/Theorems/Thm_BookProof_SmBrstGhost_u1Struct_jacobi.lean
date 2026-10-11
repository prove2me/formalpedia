-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_u1Struct_jacobi
-- name    : BookProof.SmBrstGhost.u1Struct_jacobi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:08:09.984622+00:00
-- url     : https://prove2.me/theorems/585f4fbc-a3c1-4d42-b25a-a81676cfad3f
-- title:
--   `BookProof.SmBrstGhost.u1Struct_jacobi` (a b c h : Fin 1) : ∑ e, (u1Struct a b e * u1Struct e c h + u1Struct b c e * u1Struct e a h + u1Struct c a e * u1Struct e b h) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.u1Struct_jacobi` (a b c h : Fin 1) : ∑ e, (u1Struct a b e * u1Struct e c h + u1Struct b c e * u1Struct e a h + u1Struct c a e * u1Struct e b h) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.u1Struct_jacobi`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.u1Struct_jacobi
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.u1Struct_jacobi (a b c h : Fin 1) :
    ∑ e, (u1Struct a b e * u1Struct e c h + u1Struct b c e * u1Struct e a h
      + u1Struct c a e * u1Struct e b h) = 0 := by sorry
