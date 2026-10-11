-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_sumStruct_jacobi
-- name    : BookProof.SmBrstGhost.sumStruct_jacobi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:06:43.644991+00:00
-- url     : https://prove2.me/theorems/f4ea6523-09c5-4f20-946f-531d9984b076
-- title:
--   `BookProof.SmBrstGhost.sumStruct_jacobi` {ι κ : Type*} [Fintype ι] [Fintype κ] {f1 : ι → ι → ι → ℝ} {f2 : κ → κ → κ → ℝ} (h1 : ∀ a b c h : ι, ∑ e, (f1 a b e * f1 e...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.sumStruct_jacobi` {ι κ : Type*} [Fintype ι] [Fintype κ] {f1 : ι → ι → ι → ℝ} {f2 : κ → κ → κ → ℝ} (h1 : ∀ a b c h : ι, ∑ e, (f1 a b e * f1 e c h + f1 b c e * f1 e a h + f1 c a e * f1 e b h) = 0) (h2 : ∀ a b c h : κ, ∑ e, (f2 a b e * f2 e c h + f2 b c e * f2 e a h + f2 c a e * f2 e b h) = 0) (a b c h : ι ⊕ κ) : ∑ e, (sumStruct f1 f2 a b e * sumStruct f1 f2 e c h + sumStruct f1 f2 b c e * sumStruct f1 f2 e a h + sumStruct f1 f2 c a e * sumStruct f1 f2 e b h) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.sumStruct_jacobi`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.sumStruct_jacobi
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

theorem BookProof.SmBrstGhost.sumStruct_jacobi {ι κ : Type*} [Fintype ι] [Fintype κ] {f1 : ι → ι → ι → ℝ}
    {f2 : κ → κ → κ → ℝ}
    (h1 : ∀ a b c h : ι, ∑ e, (f1 a b e * f1 e c h + f1 b c e * f1 e a h
      + f1 c a e * f1 e b h) = 0)
    (h2 : ∀ a b c h : κ, ∑ e, (f2 a b e * f2 e c h + f2 b c e * f2 e a h
      + f2 c a e * f2 e b h) = 0)
    (a b c h : ι ⊕ κ) :
    ∑ e, (sumStruct f1 f2 a b e * sumStruct f1 f2 e c h
      + sumStruct f1 f2 b c e * sumStruct f1 f2 e a h
      + sumStruct f1 f2 c a e * sumStruct f1 f2 e b h) = 0 := by sorry
