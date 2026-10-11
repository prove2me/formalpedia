-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_jointProb_eq_normSq_weakNumerator
-- name    : BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:22.175465+00:00
-- url     : https://prove2.me/theorems/d83a3bd0-b266-44dd-b387-11e9908ede71
-- title:
--   `BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : ‖ip (postSelect V f) (projMat a *ᵥ (U *ᵥ psi))‖ ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : ‖ip (postSelect V f) (projMat a *ᵥ (U *ᵥ psi))‖ ^ 2 = jointProb U V psi f a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator
import Mathlib
import Definitions.Def_ChapterWeakValue
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

open BookProof.ChapterTrajectory

theorem BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator (U V : Matrix (Fin n) (Fin n) ℂ)
    (psi : Fin n → ℂ) (f a : Fin n) :
    ‖ip (postSelect V f) (projMat a *ᵥ (U *ᵥ psi))‖ ^ 2 = jointProb U V psi f a := by sorry
