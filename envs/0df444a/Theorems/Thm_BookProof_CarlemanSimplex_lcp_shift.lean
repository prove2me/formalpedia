-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_lcp_shift
-- name    : BookProof.CarlemanSimplex.lcp_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:47:47.741485+00:00
-- url     : https://prove2.me/theorems/974a2bd4-b4d9-49c2-9d9d-7b8c123a287e
-- title:
--   `BookProof.CarlemanSimplex.lcp_shift` (i j : Fin d) (a : Fin d →₀ ℕ) : lcp (a + pvec i j) i j = rcp a i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.lcp_shift` (i j : Fin d) (a : Fin d →₀ ℕ) : lcp (a + pvec i j) i j = rcp a i j
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.lcp_shift`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.lcp_shift
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

theorem BookProof.CarlemanSimplex.lcp_shift (i j : Fin d) (a : Fin d →₀ ℕ) :
    lcp (a + pvec i j) i j = rcp a i j := by sorry
