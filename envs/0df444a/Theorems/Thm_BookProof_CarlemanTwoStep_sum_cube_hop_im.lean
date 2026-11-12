-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_sum_cube_hop_im
-- name    : BookProof.CarlemanTwoStep.sum_cube_hop_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:50:22.876466+00:00
-- url     : https://prove2.me/theorems/22a08d61-f9c6-4e10-9232-acbcc001b7f5
-- title:
--   `BookProof.CarlemanTwoStep.sum_cube_hop_im` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.sum_cube_hop_im` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i) (hvan : ∀ a : Fin d →₀ ℕ, a i < k → lc a i = 0) (N : ℕ) : (∑ a ∈ cube d N, (rtermG u w rc k i a + ltermG u w lc k i a)).im = (∑ a ∈ faceK d N i k, rtermG u w rc k i a).im
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.sum_cube_hop_im`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.sum_cube_hop_im
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}

theorem BookProof.CarlemanTwoStep.sum_cube_hop_im {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i)
    (hvan : ∀ a : Fin d →₀ ℕ, a i < k → lc a i = 0) (N : ℕ) :
    (∑ a ∈ cube d N, (rtermG u w rc k i a + ltermG u w lc k i a)).im
      = (∑ a ∈ faceK d N i k, rtermG u w rc k i a).im := by sorry
