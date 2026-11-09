-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_lc2_shift
-- name    : BookProof.CarlemanTwoStep.lc2_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:51:15.624369+00:00
-- url     : https://prove2.me/theorems/7e061ee7-3efc-4cd5-9f7b-589740cbf0a3
-- title:
--   `BookProof.CarlemanTwoStep.lc2_shift` (i : Fin d) (a : Fin d →₀ ℕ) : lc2 (a + Finsupp.single i 2) i = rc2 a i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.lc2_shift` (i : Fin d) (a : Fin d →₀ ℕ) : lc2 (a + Finsupp.single i 2) i = rc2 a i
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.lc2_shift`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.lc2_shift
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

theorem BookProof.CarlemanTwoStep.lc2_shift (i : Fin d) (a : Fin d →₀ ℕ) :
    lc2 (a + Finsupp.single i 2) i = rc2 a i := by sorry
