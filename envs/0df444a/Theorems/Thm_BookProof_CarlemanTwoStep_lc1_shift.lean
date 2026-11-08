-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_lc1_shift
-- name    : BookProof.CarlemanTwoStep.lc1_shift
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:50:56.069771+00:00
-- url     : https://prove2.me/theorems/041fb2aa-1e37-474d-8ed2-38c388df36ae
-- title:
--   `BookProof.CarlemanTwoStep.lc1_shift` (i : Fin d) (a : Fin d →₀ ℕ) : lc1 (a + Finsupp.single i 1) i = rc1 a i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.lc1_shift` (i : Fin d) (a : Fin d →₀ ℕ) : lc1 (a + Finsupp.single i 1) i = rc1 a i
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.lc1_shift`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.lc1_shift
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

theorem BookProof.CarlemanTwoStep.lc1_shift (i : Fin d) (a : Fin d →₀ ℕ) :
    lc1 (a + Finsupp.single i 1) i = rc1 a i := by sorry
