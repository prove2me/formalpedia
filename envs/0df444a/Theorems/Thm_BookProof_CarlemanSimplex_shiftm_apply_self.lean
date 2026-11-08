-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_shiftm_apply_self
-- name    : BookProof.CarlemanSimplex.shiftm_apply_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:46:46.978132+00:00
-- url     : https://prove2.me/theorems/e6f0f409-aded-4176-aa64-089637550e0c
-- title:
--   `BookProof.CarlemanSimplex.shiftm_apply_self` {a : Fin d →₀ ℕ} {i j : Fin d} : (shiftm a i j) i = (a - Finsupp.single j 1 : Fin d →₀ ℕ) i + 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.shiftm_apply_self` {a : Fin d →₀ ℕ} {i j : Fin d} : (shiftm a i j) i = (a - Finsupp.single j 1 : Fin d →₀ ℕ) i + 1
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.shiftm_apply_self`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.shiftm_apply_self
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

theorem BookProof.CarlemanSimplex.shiftm_apply_self {a : Fin d →₀ ℕ} {i j : Fin d} :
    (shiftm a i j) i = (a - Finsupp.single j 1 : Fin d →₀ ℕ) i + 1 := by sorry
