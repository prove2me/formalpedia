-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_matterGen_lie
-- name    : BookProof.SmBrstGhost.matterGen_lie
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:25:59.827983+00:00
-- url     : https://prove2.me/theorems/047dd932-4081-4e40-ab41-9abcbbbe70a2
-- title:
--   `BookProof.SmBrstGhost.matterGen_lie` {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ} {f : Fin 12 → Fin 12 → Fin 12 → ℝ} (hT : ClosesWithStructureConstants T f) (a b : Fin 12) : ma
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.matterGen_lie` {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ} {f : Fin 12 → Fin 12 → Fin 12 → ℝ} (hT : ClosesWithStructureConstants T f) (a b : Fin 12) : matterGen m T a * matterGen m T b - matterGen m T b * matterGen m T a = ∑ c, f a b c • matterGen m T c
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.matterGen_lie`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.matterGen_lie
import Definitions.Def_ChapterBRSTNilpotent
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmCar
open BookProof.YangMillsSU3
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.matterGen_lie {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f : Fin 12 → Fin 12 → Fin 12 → ℝ} (hT : ClosesWithStructureConstants T f) (a b : Fin 12) :
    matterGen m T a * matterGen m T b - matterGen m T b * matterGen m T a
      = ∑ c, f a b c • matterGen m T c := by sorry
