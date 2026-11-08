-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_mem_simplexF
-- name    : BookProof.CarlemanSimplex.mem_simplexF
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:45:26.090285+00:00
-- url     : https://prove2.me/theorems/dfadd187-1c06-4814-a7f4-2deeeb9143b4
-- title:
--   `BookProof.CarlemanSimplex.mem_simplexF` {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ simplexF d N ↔ deg a ≤ N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.mem_simplexF` {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ simplexF d N ↔ deg a ≤ N
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.mem_simplexF`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.mem_simplexF
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteCarleman
open BookProof.CarlemanSimplex



open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanSimplex.mem_simplexF {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ simplexF d N ↔ deg a ≤ N := by sorry
