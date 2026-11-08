-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_shiftm_shiftm
-- name    : BookProof.CarlemanSimplex.shiftm_shiftm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:47:12.327867+00:00
-- url     : https://prove2.me/theorems/999720c7-3711-4506-a52e-2683250c3616
-- title:
--   `BookProof.CarlemanSimplex.shiftm_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : shiftm (shiftm a i j) j i = a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.shiftm_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : shiftm (shiftm a i j) j i = a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.shiftm_shiftm`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.shiftm_shiftm
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

theorem BookProof.CarlemanSimplex.shiftm_shiftm {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) :
    shiftm (shiftm a i j) j i = a := by sorry
