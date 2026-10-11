-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_embedMatter_sub
-- name    : BookProof.SmBrstGhost.embedMatter_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:25:42.256667+00:00
-- url     : https://prove2.me/theorems/6dd6eef9-9f4e-4c70-be44-a91728f86af7
-- title:
--   `BookProof.SmBrstGhost.embedMatter_sub` (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) : embedMatter m (M - P) = embedMatter m M - embedMatter m P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.embedMatter_sub` (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) : embedMatter m (M - P) = embedMatter m M - embedMatter m P
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.embedMatter_sub`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.embedMatter_sub
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.embedMatter_sub (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m (M - P) = embedMatter m M - embedMatter m P := by sorry
