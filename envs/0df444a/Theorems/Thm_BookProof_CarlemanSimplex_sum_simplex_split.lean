-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_sum_simplex_split
-- name    : BookProof.CarlemanSimplex.sum_simplex_split
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:45:40.038577+00:00
-- url     : https://prove2.me/theorems/edad6f08-7750-47ab-b269-feee67cc7910
-- title:
--   `BookProof.CarlemanSimplex.sum_simplex_split` (d N k : ℕ) (F : (Fin d →₀ ℕ) → ℂ) : ∑ a ∈ simplexF d N, F a = ∑ a ∈ sInn d N k, F a + ∑ a ∈ sBd d N k, F a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.sum_simplex_split` (d N k : ℕ) (F : (Fin d →₀ ℕ) → ℂ) : ∑ a ∈ simplexF d N, F a = ∑ a ∈ sInn d N k, F a + ∑ a ∈ sBd d N k, F a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.sum_simplex_split`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.sum_simplex_split
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

theorem BookProof.CarlemanSimplex.sum_simplex_split (d N k : ℕ) (F : (Fin d →₀ ℕ) → ℂ) :
    ∑ a ∈ simplexF d N, F a = ∑ a ∈ sInn d N k, F a + ∑ a ∈ sBd d N k, F a := by sorry
