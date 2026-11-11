-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_sBd_subset_simplexF
-- name    : BookProof.CarlemanSimplex.sBd_subset_simplexF
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:45:49.430006+00:00
-- url     : https://prove2.me/theorems/1b34003b-be3c-4226-a09a-94c687e19902
-- title:
--   `BookProof.CarlemanSimplex.sBd_subset_simplexF` (d N k : ℕ) : sBd d N k ⊆ simplexF d N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.sBd_subset_simplexF` (d N k : ℕ) : sBd d N k ⊆ simplexF d N
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.sBd_subset_simplexF`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.sBd_subset_simplexF
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

theorem BookProof.CarlemanSimplex.sBd_subset_simplexF (d N k : ℕ) : sBd d N k ⊆ simplexF d N := by sorry
