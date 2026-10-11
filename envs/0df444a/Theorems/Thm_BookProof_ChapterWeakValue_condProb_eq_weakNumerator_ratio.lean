-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_condProb_eq_weakNumerator_ratio
-- name    : BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:14:51.703633+00:00
-- url     : https://prove2.me/theorems/a3ff0959-ccbd-4369-9b6a-de9420e2aecf
-- title:
--   `BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : condProb U V psi f a = ‖ip (postSelect V f) (projMat
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : condProb U V psi f a = ‖ip (postSelect V f) (projMat a *ᵥ (U *ᵥ psi))‖ ^ 2 / ∑ b, ‖ip (postSelect V f) (projMat b *ᵥ (U *ᵥ psi))‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio
import Mathlib
import Definitions.Def_ChapterWeakValue
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

open BookProof.ChapterTrajectory

theorem BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio (U V : Matrix (Fin n) (Fin n) ℂ)
    (psi : Fin n → ℂ) (f a : Fin n) :
    condProb U V psi f a =
      ‖ip (postSelect V f) (projMat a *ᵥ (U *ᵥ psi))‖ ^ 2 /
        ∑ b, ‖ip (postSelect V f) (projMat b *ᵥ (U *ᵥ psi))‖ ^ 2 := by sorry
