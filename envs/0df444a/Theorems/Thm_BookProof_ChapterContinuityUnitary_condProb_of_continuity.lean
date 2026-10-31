-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_condProb_of_continuity
-- name    : BookProof.ChapterContinuityUnitary.condProb_of_continuity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:07:08.510868+00:00
-- url     : https://prove2.me/theorems/207d08b7-c852-48c2-9750-7dac9abb9027
-- title:
--   The Lean 4 theorem `condProb_of_continuity` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `condProb_of_continuity` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.condProb_of_continuity
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]
variable {X : Type*}


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.condProb_of_continuity (v : X → (ZMod N → ℝ)) (t : ℝ)
    (psi : X → ZMod N → ℂ) (hpsi : ∀ x, ∑ z, ‖psi x z‖ ^ 2 = 1) (x : X) :
    (∑' z, bornPMF (v x) t (psi x) (hpsi x) z) = 1 ∧
      ∀ B : Finset (ZMod N),
        ∑ z ∈ B, bornPMF (v x) t (psi x) (hpsi x) z
          = ENNReal.ofReal (bornRecover (v x) t (psi x) B) := by sorry
