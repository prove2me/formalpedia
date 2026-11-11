-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_sum_ltermP
-- name    : BookProof.CarlemanSimplex.sum_ltermP
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:45:58.459214+00:00
-- url     : https://prove2.me/theorems/91240b33-4ff0-4712-a1ea-f269f2cc9de7
-- title:
--   `BookProof.CarlemanSimplex.sum_ltermP` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a) (hvan : ∀ a : Fin d →₀...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.sum_ltermP` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a) (hvan : ∀ a : Fin d →₀ ℕ, ¬ P ≤ a → lc a = 0) (N : ℕ) : ∑ a ∈ simplexF d N, ltermP u w lc P a = (starRingEnd ℂ) (∑ b ∈ sInn d N (deg P), rtermP u w rc P b)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.sum_ltermP`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.sum_ltermP
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

theorem BookProof.CarlemanSimplex.sum_ltermP {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a)
    (hvan : ∀ a : Fin d →₀ ℕ, ¬ P ≤ a → lc a = 0) (N : ℕ) :
    ∑ a ∈ simplexF d N, ltermP u w lc P a
      = (starRingEnd ℂ) (∑ b ∈ sInn d N (deg P), rtermP u w rc P b) := by sorry
