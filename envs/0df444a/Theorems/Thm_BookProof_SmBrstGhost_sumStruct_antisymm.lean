-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_sumStruct_antisymm
-- name    : BookProof.SmBrstGhost.sumStruct_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:06:33.96531+00:00
-- url     : https://prove2.me/theorems/2498b31b-5115-4cb0-a6d3-9fbc911c35a4
-- title:
--   `BookProof.SmBrstGhost.sumStruct_antisymm` {ι κ : Type*} {f1 : ι → ι → ι → ℝ} {f2 : κ → κ → κ → ℝ} (h1 : ∀ a b c, f1 a b c = -f1 b a c) (h2 : ∀ a b c, f2 a b c = -f2 b...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.sumStruct_antisymm` {ι κ : Type*} {f1 : ι → ι → ι → ℝ} {f2 : κ → κ → κ → ℝ} (h1 : ∀ a b c, f1 a b c = -f1 b a c) (h2 : ∀ a b c, f2 a b c = -f2 b a c) (a b c : ι ⊕ κ) : sumStruct f1 f2 a b c = -sumStruct f1 f2 b a c
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.sumStruct_antisymm`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.sumStruct_antisymm
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.sumStruct_antisymm {ι κ : Type*} {f1 : ι → ι → ι → ℝ}
    {f2 : κ → κ → κ → ℝ} (h1 : ∀ a b c, f1 a b c = -f1 b a c)
    (h2 : ∀ a b c, f2 a b c = -f2 b a c) (a b c : ι ⊕ κ) :
    sumStruct f1 f2 a b c = -sumStruct f1 f2 b a c := by sorry
