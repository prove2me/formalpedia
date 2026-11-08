-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_sub_add_singleK
-- name    : BookProof.CarlemanTwoStep.sub_add_singleK
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:49:34.869304+00:00
-- url     : https://prove2.me/theorems/6e81d9fe-6c07-4ab4-804e-d66377ed5ff1
-- title:
--   `BookProof.CarlemanTwoStep.sub_add_singleK` {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} (h : k ≤ a i) : (a - Finsupp.single i k) + Finsupp.single i k = a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.sub_add_singleK` {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} (h : k ≤ a i) : (a - Finsupp.single i k) + Finsupp.single i k = a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.sub_add_singleK`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.sub_add_singleK
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanTwoStep.sub_add_singleK {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} (h : k ≤ a i) :
    (a - Finsupp.single i k) + Finsupp.single i k = a := by sorry
