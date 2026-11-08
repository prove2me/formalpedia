-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_sub_singleK_apply
-- name    : BookProof.CarlemanTwoStep.sub_singleK_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:49:46.610421+00:00
-- url     : https://prove2.me/theorems/94a99cb5-842b-4c05-add0-d63933fb62f8
-- title:
--   `BookProof.CarlemanTwoStep.sub_singleK_apply` {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} : (a - Finsupp.single i k : Fin d →₀ ℕ) i = a i - k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.sub_singleK_apply` {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} : (a - Finsupp.single i k : Fin d →₀ ℕ) i = a i - k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.sub_singleK_apply`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.sub_singleK_apply
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanTwoStep.sub_singleK_apply {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    (a - Finsupp.single i k : Fin d →₀ ℕ) i = a i - k := by sorry
