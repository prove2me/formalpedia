-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_sum_mterm_im
-- name    : BookProof.CarlemanSimplex.sum_mterm_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:47:34.603673+00:00
-- url     : https://prove2.me/theorems/b0e06c72-f217-4161-801e-45d32b992bb1
-- title:
--   `BookProof.CarlemanSimplex.sum_mterm_im` {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j)) (N : ℕ) : (∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j).im = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.sum_mterm_im` {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j)) (N : ℕ) : (∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.sum_mterm_im`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.sum_mterm_im
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

theorem BookProof.CarlemanSimplex.sum_mterm_im {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (N : ℕ) : (∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j).im = 0 := by sorry
