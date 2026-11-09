-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_rc1_nonneg
-- name    : BookProof.CarlemanTwoStep.rc1_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:51:18.333463+00:00
-- url     : https://prove2.me/theorems/8c76a3ad-1867-441d-b6fd-df84eaa97959
-- title:
--   `BookProof.CarlemanTwoStep.rc1_nonneg` (a : Fin d →₀ ℕ) (i : Fin d) : 0 ≤ rc1 a i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.rc1_nonneg` (a : Fin d →₀ ℕ) (i : Fin d) : 0 ≤ rc1 a i
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.rc1_nonneg`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.rc1_nonneg
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}

theorem BookProof.CarlemanTwoStep.rc1_nonneg (a : Fin d →₀ ℕ) (i : Fin d) : 0 ≤ rc1 a i := by sorry
