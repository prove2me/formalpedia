-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_facesK_le
-- name    : BookProof.CarlemanTwoStep.facesK_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:52:27.165983+00:00
-- url     : https://prove2.me/theorems/c1edfb61-fef9-4dfd-ad7d-66a546044529
-- title:
--   `BookProof.CarlemanTwoStep.facesK_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ faceK d...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.facesK_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u a‖ ^ 2 ≤ (k : ℝ) * B
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.facesK_le`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.facesK_le
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

theorem BookProof.CarlemanTwoStep.facesK_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u a‖ ^ 2 ≤ (k : ℝ) * B := by sorry
