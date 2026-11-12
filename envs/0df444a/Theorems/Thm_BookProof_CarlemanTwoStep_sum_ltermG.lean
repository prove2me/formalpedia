-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_sum_ltermG
-- name    : BookProof.CarlemanTwoStep.sum_ltermG
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:50:08.97831+00:00
-- url     : https://prove2.me/theorems/0aacf9b9-0d51-47ca-b4ba-5db18162e066
-- title:
--   `BookProof.CarlemanTwoStep.sum_ltermG` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.sum_ltermG` {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d} (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i) (hvan : ∀ a : Fin d →₀ ℕ, a i < k → lc a i = 0) (N : ℕ) : ∑ a ∈ cube d N, ltermG u w lc k i a = (starRingEnd ℂ) (∑ a ∈ innK d N i k, rtermG u w rc k i a)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.sum_ltermG`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.sum_ltermG
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

theorem BookProof.CarlemanTwoStep.sum_ltermG {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i)
    (hvan : ∀ a : Fin d →₀ ℕ, a i < k → lc a i = 0) (N : ℕ) :
    ∑ a ∈ cube d N, ltermG u w lc k i a
      = (starRingEnd ℂ) (∑ a ∈ innK d N i k, rtermG u w rc k i a) := by sorry
