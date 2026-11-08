-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_apply_le_deg
-- name    : BookProof.CarlemanSimplex.apply_le_deg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:44:37.084495+00:00
-- url     : https://prove2.me/theorems/0c17d883-d498-49c5-ad4d-d8ab60ea0497
-- title:
--   `BookProof.CarlemanSimplex.apply_le_deg` (a : Fin d →₀ ℕ) (i : Fin d) : a i ≤ deg a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.apply_le_deg` (a : Fin d →₀ ℕ) (i : Fin d) : a i ≤ deg a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.apply_le_deg`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.apply_le_deg
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

theorem BookProof.CarlemanSimplex.apply_le_deg (a : Fin d →₀ ℕ) (i : Fin d) : a i ≤ deg a := by sorry
