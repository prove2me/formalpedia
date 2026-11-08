-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_sum_range_of_multiplicity
-- name    : BookProof.CarlemanTwoStep.sum_range_of_multiplicity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:51:45.043439+00:00
-- url     : https://prove2.me/theorems/f7ea594f-bb19-4aec-9221-28422bf2d64e
-- title:
--   `BookProof.CarlemanTwoStep.sum_range_of_multiplicity` {B : ℝ} (m : ℕ) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (G : ℕ → Finset (Fin d →₀ ℕ)) (hm...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.sum_range_of_multiplicity` {B : ℝ} (m : ℕ) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (G : ℕ → Finset (Fin d →₀ ℕ)) (hm : ∀ (a : Fin d →₀ ℕ) (M : ℕ), (((Finset.range M).filter (fun N => a ∈ G N)).card) ≤ m) (M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ (m : ℝ) * B
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.sum_range_of_multiplicity`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.sum_range_of_multiplicity
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

theorem BookProof.CarlemanTwoStep.sum_range_of_multiplicity {B : ℝ} (m : ℕ)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (G : ℕ → Finset (Fin d →₀ ℕ))
    (hm : ∀ (a : Fin d →₀ ℕ) (M : ℕ),
      (((Finset.range M).filter (fun N => a ∈ G N)).card) ≤ m)
    (M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ (m : ℝ) * B := by sorry
