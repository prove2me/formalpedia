-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_deg_pvec
-- name    : BookProof.CarlemanSimplex.deg_pvec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:47:58.102072+00:00
-- url     : https://prove2.me/theorems/3c0bd981-9798-4a89-9e85-d73e7077d1ac
-- title:
--   `BookProof.CarlemanSimplex.deg_pvec` (i j : Fin d) : deg (pvec (d := d) i j) = 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.deg_pvec` (i j : Fin d) : deg (pvec (d := d) i j) = 2
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.deg_pvec`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.deg_pvec
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

theorem BookProof.CarlemanSimplex.deg_pvec (i j : Fin d) : deg (pvec (d := d) i j) = 2 := by sorry
