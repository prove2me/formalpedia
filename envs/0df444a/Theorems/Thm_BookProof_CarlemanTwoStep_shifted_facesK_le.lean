-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_shifted_facesK_le
-- name    : BookProof.CarlemanTwoStep.shifted_facesK_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:52:29.910505+00:00
-- url     : https://prove2.me/theorems/6067016a-1813-4955-a847-ef44be422e18
-- title:
--   `BookProof.CarlemanTwoStep.shifted_facesK_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.shifted_facesK_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2 ≤ (k : ℝ) * B
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.shifted_facesK_le`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.shifted_facesK_le
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanTwoStep.shifted_facesK_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2
      ≤ (k : ℝ) * B := by sorry
