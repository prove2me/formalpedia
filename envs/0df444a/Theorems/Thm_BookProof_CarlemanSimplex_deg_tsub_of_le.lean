-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_deg_tsub_of_le
-- name    : BookProof.CarlemanSimplex.deg_tsub_of_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:45:54.106195+00:00
-- url     : https://prove2.me/theorems/5e076266-20b3-40b5-9c99-2ddeb6631f29
-- title:
--   `BookProof.CarlemanSimplex.deg_tsub_of_le` {P a : Fin d →₀ ℕ} (h : P ≤ a) : deg (a - P) + deg P = deg a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.deg_tsub_of_le` {P a : Fin d →₀ ℕ} (h : P ≤ a) : deg (a - P) + deg P = deg a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.deg_tsub_of_le`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.deg_tsub_of_le
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

theorem BookProof.CarlemanSimplex.deg_tsub_of_le {P a : Fin d →₀ ℕ} (h : P ≤ a) : deg (a - P) + deg P = deg a := by sorry
