-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_tsub_add_cancel_of_le_prime
-- name    : BookProof.CarlemanSimplex.tsub_add_cancel_of_le_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:44:59.627822+00:00
-- url     : https://prove2.me/theorems/59bfb623-27fd-441d-8cf6-41dd21d31364
-- title:
--   BookProof.CarlemanSimplex.tsub_add_cancel_of_le'
-- statement:
--   BookProof.CarlemanSimplex.tsub_add_cancel_of_le'

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.tsub_add_cancel_of_le'
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

theorem BookProof.CarlemanSimplex.tsub_add_cancel_of_le_prime {P a : Fin d →₀ ℕ} (h : P ≤ a) : a - P + P = a := by sorry
