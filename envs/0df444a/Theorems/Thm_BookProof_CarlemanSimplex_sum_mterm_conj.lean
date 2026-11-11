-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_sum_mterm_conj
-- name    : BookProof.CarlemanSimplex.sum_mterm_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:47:07.461233+00:00
-- url     : https://prove2.me/theorems/dac64d07-a49e-4343-afc3-ea23e04eb99a
-- title:
--   `BookProof.CarlemanSimplex.sum_mterm_conj` {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j)) (N : ℕ) (i j : Fin d) : (starRingEnd ℂ) (∑ a ∈ simplexF d N, mterm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.sum_mterm_conj` {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j)) (N : ℕ) (i j : Fin d) : (starRingEnd ℂ) (∑ a ∈ simplexF d N, mterm u M a i j) = ∑ b ∈ simplexF d N, mterm u M b j i
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.sum_mterm_conj`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.sum_mterm_conj
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

theorem BookProof.CarlemanSimplex.sum_mterm_conj {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (N : ℕ) (i j : Fin d) :
    (starRingEnd ℂ) (∑ a ∈ simplexF d N, mterm u M a i j)
      = ∑ b ∈ simplexF d N, mterm u M b j i := by sorry
