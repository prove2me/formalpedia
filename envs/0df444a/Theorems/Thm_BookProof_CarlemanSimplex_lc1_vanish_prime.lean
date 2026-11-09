-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_lc1_vanish_prime
-- name    : BookProof.CarlemanSimplex.lc1_vanish_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:48:10.254605+00:00
-- url     : https://prove2.me/theorems/65b49c71-aade-40dd-b207-b668455b64e3
-- title:
--   BookProof.CarlemanSimplex.lc1_vanish'
-- statement:
--   BookProof.CarlemanSimplex.lc1_vanish'

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.lc1_vanish'
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
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanSimplex.lc1_vanish_prime (i : Fin d) (a : Fin d →₀ ℕ) (h : ¬ Finsupp.single i 1 ≤ a) :
    lc1 a i = 0 := by sorry
