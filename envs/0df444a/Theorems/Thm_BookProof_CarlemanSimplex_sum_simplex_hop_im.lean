-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_sum_simplex_hop_im
-- name    : BookProof.CarlemanSimplex.sum_simplex_hop_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:46:29.159135+00:00
-- url     : https://prove2.me/theorems/487bd51a-fc44-45b2-a5d2-d6be0fcdb66e
-- title:
--   `BookProof.CarlemanSimplex.sum_simplex_hop_im` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a) (hvan : ∀ a : Fin d...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.sum_simplex_hop_im` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a) (hvan : ∀ a : Fin d →₀ ℕ, ¬ P ≤ a → lc a = 0) (N : ℕ) : (∑ a ∈ simplexF d N, (rtermP u w rc P a + ltermP u w lc P a)).im = (∑ a ∈ sBd d N (deg P), rtermP u w rc P a).im
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.sum_simplex_hop_im`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.sum_simplex_hop_im
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

theorem BookProof.CarlemanSimplex.sum_simplex_hop_im {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a)
    (hvan : ∀ a : Fin d →₀ ℕ, ¬ P ≤ a → lc a = 0) (N : ℕ) :
    (∑ a ∈ simplexF d N, (rtermP u w rc P a + ltermP u w lc P a)).im
      = (∑ a ∈ sBd d N (deg P), rtermP u w rc P a).im := by sorry
