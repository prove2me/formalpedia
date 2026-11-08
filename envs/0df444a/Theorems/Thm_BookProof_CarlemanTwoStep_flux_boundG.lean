-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_flux_boundG
-- name    : BookProof.CarlemanTwoStep.flux_boundG
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:51:46.90463+00:00
-- url     : https://prove2.me/theorems/e7175d6d-aa16-4a40-a215-88f8cdaa496d
-- title:
--   `BookProof.CarlemanTwoStep.flux_boundG` {w : ℂ} {rc : (Fin d →₀ ℕ) → Fin d → ℝ} (N : ℕ) (i : Fin d) (k : ℕ) {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ faceK d N i k, |rc a i|...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.flux_boundG` {w : ℂ} {rc : (Fin d →₀ ℕ) → Fin d → ℝ} (N : ℕ) (i : Fin d) (k : ℕ) {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ faceK d N i k, |rc a i| ≤ Cn) : |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im| ≤ Cn * (‖w‖ * ((∑ a ∈ faceK d N i k, (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.flux_boundG`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.flux_boundG
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

theorem BookProof.CarlemanTwoStep.flux_boundG {w : ℂ} {rc : (Fin d →₀ ℕ) → Fin d → ℝ} (N : ℕ) (i : Fin d) (k : ℕ)
    {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ faceK d N i k, |rc a i| ≤ Cn) :
    |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im|
      ≤ Cn * (‖w‖ * ((∑ a ∈ faceK d N i k,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2)) := by sorry
