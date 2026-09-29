-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_temple_lower_bound
-- name    : BookProof.SirkFinitePrecision.temple_lower_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:14:02.175389+00:00
-- url     : https://prove2.me/theorems/fb672ebf-0732-4b49-abf2-94662b56ebd5
-- title:
--   Temple's inequality.** The honest a-posteriori *lower* bound for the lowest eigenvalue: if every eigenvalue is either `lam0` (the lowest) or at least `β`, and the computed Rayleigh quotien
-- statement:
--   **Temple's inequality.**  The honest a-posteriori *lower* bound for the lowest
--   eigenvalue: if every eigenvalue is either `lam0` (the lowest) or at least `β`, and
--   the computed Rayleigh quotient `θ` of a unit vector satisfies `θ < β`, then
--   `lam0 ≥ θ − (‖T x‖² − θ²)/(β − θ)`.  The numerator `‖T x‖² − θ²` is the squared
--   residual of the computed vector.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.temple_lower_bound` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 253–295.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L253-L295

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.temple_lower_bound
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.temple_lower_bound {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) {lam0 β : ℝ}
    (hsep : ∀ i, hT.eigenvalues hn i = lam0 ∨ β ≤ hT.eigenvalues hn i)
    (hlow : ∀ i, lam0 ≤ hT.eigenvalues hn i)
    (hβ : rayleigh T x < β) :
    rayleigh T x - (‖T x‖ ^ 2 - rayleigh T x ^ 2) / (β - rayleigh T x) ≤ lam0 := by sorry
