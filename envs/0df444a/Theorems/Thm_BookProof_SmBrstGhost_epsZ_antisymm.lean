-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_epsZ_antisymm
-- name    : BookProof.SmBrstGhost.epsZ_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:09:29.128694+00:00
-- url     : https://prove2.me/theorems/6041ba70-26c3-495b-ad85-e663f4df28a9
-- title:
--   `BookProof.SmBrstGhost.epsZ_antisymm` : ∀ a b c : Fin 3, epsZ a b c = -epsZ b a c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.epsZ_antisymm` : ∀ a b c : Fin 3, epsZ a b c = -epsZ b a c
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.epsZ_antisymm`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.epsZ_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.epsZ_antisymm : ∀ a b c : Fin 3, epsZ a b c = -epsZ b a c := by sorry
