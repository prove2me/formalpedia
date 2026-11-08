-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_rcm_of_zero
-- name    : BookProof.CarlemanSimplex.rcm_of_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:46:40.473973+00:00
-- url     : https://prove2.me/theorems/cb7e8158-4430-449b-b2ba-be4bcec630e9
-- title:
--   `BookProof.CarlemanSimplex.rcm_of_zero` {a : Fin d →₀ ℕ} {i j : Fin d} (h : a j = 0) : rcm a i j = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.rcm_of_zero` {a : Fin d →₀ ℕ} {i j : Fin d} (h : a j = 0) : rcm a i j = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.rcm_of_zero`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.rcm_of_zero
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanSimplex



open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}

theorem BookProof.CarlemanSimplex.rcm_of_zero {a : Fin d →₀ ℕ} {i j : Fin d} (h : a j = 0) : rcm a i j = 0 := by sorry
