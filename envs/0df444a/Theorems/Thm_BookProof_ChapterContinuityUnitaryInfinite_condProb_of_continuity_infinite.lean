-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_condProb_of_continuity_infinite
-- name    : BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:35:14.013224+00:00
-- url     : https://prove2.me/theorems/e05bf69a-d465-43a2-aa6a-c9b59aa4fe72
-- title:
--   (v : X → LinfZ) (t : ℝ) (psi : X → L2Z) (hpsi : ∀ x, ‖psi x‖ = 1) (x : X) : (∑' z : ℤ, bornPMF (v x) t (psi x) (hpsi x) z) = 1 ∧ ∀ B : Finset ℤ, ∑ z ∈ B, bornPMF (v x) t...
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite


open scoped ENNReal InnerProductSpace

variable {X : Type*}

theorem BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite (v : X → LinfZ) (t : ℝ) (psi : X → L2Z)
    (hpsi : ∀ x, ‖psi x‖ = 1) (x : X) :
    (∑' z : ℤ, bornPMF (v x) t (psi x) (hpsi x) z) = 1 ∧
      ∀ B : Finset ℤ,
        ∑ z ∈ B, bornPMF (v x) t (psi x) (hpsi x) z
          = ENNReal.ofReal (bornRecover (v x) t (psi x) B) := by sorry
