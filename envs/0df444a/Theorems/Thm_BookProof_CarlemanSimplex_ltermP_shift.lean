-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_ltermP_shift
-- name    : BookProof.CarlemanSimplex.ltermP_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:45:57.185713+00:00
-- url     : https://prove2.me/theorems/3df8eff8-58c6-40c1-ab81-177e7ef1fd37
-- title:
--   `BookProof.CarlemanSimplex.ltermP_shift` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a) (b : Fin d →₀ ℕ) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.ltermP_shift` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a) (b : Fin d →₀ ℕ) : ltermP u w lc P (b + P) = (starRingEnd ℂ) (rtermP u w rc P b)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.ltermP_shift`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.ltermP_shift
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

theorem BookProof.CarlemanSimplex.ltermP_shift {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a) (b : Fin d →₀ ℕ) :
    ltermP u w lc P (b + P) = (starRingEnd ℂ) (rtermP u w rc P b) := by sorry
