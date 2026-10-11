-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_epsZ_jacobi
-- name    : BookProof.SmBrstGhost.epsZ_jacobi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:07:17.72863+00:00
-- url     : https://prove2.me/theorems/9a063557-7d43-4d9b-87b2-db6b5a1f3c42
-- title:
--   `BookProof.SmBrstGhost.epsZ_jacobi` : ∀ a b c h : Fin 3, ∑ e, (epsZ a b e * epsZ e c h + epsZ b c e * epsZ e a h + epsZ c a e * epsZ e b h) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.epsZ_jacobi` : ∀ a b c h : Fin 3, ∑ e, (epsZ a b e * epsZ e c h + epsZ b c e * epsZ e a h + epsZ c a e * epsZ e b h) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.epsZ_jacobi`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.epsZ_jacobi
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.epsZ_jacobi : ∀ a b c h : Fin 3,
    ∑ e, (epsZ a b e * epsZ e c h + epsZ b c e * epsZ e a h + epsZ c a e * epsZ e b h) = 0 := by sorry
