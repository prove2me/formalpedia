-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_deg_shiftm
-- name    : BookProof.CarlemanSimplex.deg_shiftm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:46:55.738148+00:00
-- url     : https://prove2.me/theorems/5a3cc969-0b65-4cd8-b0da-2c0e0df459e7
-- title:
--   `BookProof.CarlemanSimplex.deg_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : deg (shiftm a i j) = deg a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.deg_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : deg (shiftm a i j) = deg a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.deg_shiftm`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.deg_shiftm
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

theorem BookProof.CarlemanSimplex.deg_shiftm {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : deg (shiftm a i j) = deg a := by sorry
