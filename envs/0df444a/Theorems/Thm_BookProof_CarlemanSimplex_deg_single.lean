-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_deg_single
-- name    : BookProof.CarlemanSimplex.deg_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:44:57.850521+00:00
-- url     : https://prove2.me/theorems/0d015ecc-0ca2-42ee-9ef9-b91c3f6bbf46
-- title:
--   `BookProof.CarlemanSimplex.deg_single` (i : Fin d) (k : ℕ) : deg (Finsupp.single i k) = k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.deg_single` (i : Fin d) (k : ℕ) : deg (Finsupp.single i k) = k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.deg_single`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.deg_single
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

theorem BookProof.CarlemanSimplex.deg_single (i : Fin d) (k : ℕ) : deg (Finsupp.single i k) = k := by sorry
