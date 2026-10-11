-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_smStruct_antisymm
-- name    : BookProof.SmBrstGhost.smStruct_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:07:41.617207+00:00
-- url     : https://prove2.me/theorems/e833323a-01e0-4c61-b4a1-6f38040d0feb
-- title:
--   `BookProof.SmBrstGhost.smStruct_antisymm` {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} (h3 : ∀ a b c, f3 a b c = -f3 b a c) (a b c : Fin 12) : smStruct f3 a b c = -smStruct f3 b a c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.smStruct_antisymm` {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} (h3 : ∀ a b c, f3 a b c = -f3 b a c) (a b c : Fin 12) : smStruct f3 a b c = -smStruct f3 b a c
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.smStruct_antisymm`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.smStruct_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.smStruct_antisymm {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (h3 : ∀ a b c, f3 a b c = -f3 b a c) (a b c : Fin 12) :
    smStruct f3 a b c = -smStruct f3 b a c := by sorry
