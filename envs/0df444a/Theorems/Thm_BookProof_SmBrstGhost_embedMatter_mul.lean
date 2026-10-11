-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_embedMatter_mul
-- name    : BookProof.SmBrstGhost.embedMatter_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:25:48.302982+00:00
-- url     : https://prove2.me/theorems/4df13ba1-764f-4c59-8d19-bfb3245e7837
-- title:
--   `BookProof.SmBrstGhost.embedMatter_mul` (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) : embedMatter m M * embedMatter m P = embedMatter m (M * P)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.embedMatter_mul` (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) : embedMatter m M * embedMatter m P = embedMatter m (M * P)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.embedMatter_mul`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.embedMatter_mul
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

theorem BookProof.SmBrstGhost.embedMatter_mul (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m M * embedMatter m P = embedMatter m (M * P) := by sorry
