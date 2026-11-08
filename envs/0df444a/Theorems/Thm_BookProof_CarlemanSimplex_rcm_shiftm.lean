-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_rcm_shiftm
-- name    : BookProof.CarlemanSimplex.rcm_shiftm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:47:05.822884+00:00
-- url     : https://prove2.me/theorems/b5bac611-6b48-490c-b4b4-a63c1d8d3c88
-- title:
--   `BookProof.CarlemanSimplex.rcm_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : rcm (shiftm a i j) j i = rcm a i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.rcm_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : rcm (shiftm a i j) j i = rcm a i j
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.rcm_shiftm`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.rcm_shiftm
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

theorem BookProof.CarlemanSimplex.rcm_shiftm {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) :
    rcm (shiftm a i j) j i = rcm a i j := by sorry
