-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_rcp_nonneg
-- name    : BookProof.CarlemanSimplex.rcp_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:47:46.876897+00:00
-- url     : https://prove2.me/theorems/1057ca7a-9746-49f8-af7a-12d78196ace4
-- title:
--   `BookProof.CarlemanSimplex.rcp_nonneg` (a : Fin d →₀ ℕ) (i j : Fin d) : 0 ≤ rcp a i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.rcp_nonneg` (a : Fin d →₀ ℕ) (i j : Fin d) : 0 ≤ rcp a i j
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.rcp_nonneg`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.rcp_nonneg
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

theorem BookProof.CarlemanSimplex.rcp_nonneg (a : Fin d →₀ ℕ) (i j : Fin d) : 0 ≤ rcp a i j := by sorry
