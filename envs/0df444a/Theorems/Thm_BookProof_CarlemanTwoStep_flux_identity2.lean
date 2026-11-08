-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_flux_identity2
-- name    : BookProof.CarlemanTwoStep.flux_identity2
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:51:54.109213+00:00
-- url     : https://prove2.me/theorems/2821ce18-49e9-4fe6-b6a5-2b72948a2c8c
-- title:
--   `BookProof.CarlemanTwoStep.flux_identity2` (hrec : LadderRec2 u lam w1 w2 z) (N : ℕ) : z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) = (∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.flux_identity2` (hrec : LadderRec2 u lam w1 w2 z) (N : ℕ) : z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) = (∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im) + ∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.flux_identity2`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.flux_identity2
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
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanTwoStep.flux_identity2 (hrec : LadderRec2 u lam w1 w2 z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = (∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im)
        + ∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im := by sorry
