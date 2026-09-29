-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_ground_le_rayleigh
-- name    : BookProof.SirkFinitePrecision.ground_le_rayleigh
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:13:31.239884+00:00
-- url     : https://prove2.me/theorems/8fe88258-7402-4e0f-8ac8-9a58adeb4040
-- title:
--   The lowest eigenvalue of `T` never exceeds a computed Rayleigh quotient of a unit vector: the *upper* bound is unconditional (the Rayleigh–Ritz variational principle)
-- statement:
--   The lowest eigenvalue of `T` never exceeds a computed Rayleigh quotient of a unit
--   vector: the *upper* bound is unconditional (the Rayleigh–Ritz variational
--   principle).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.ground_le_rayleigh` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 236–251.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L236-L251

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.ground_le_rayleigh
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.ground_le_rayleigh {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) {lam0 : ℝ}
    (hlow : ∀ i, lam0 ≤ hT.eigenvalues hn i) :
    lam0 ≤ rayleigh T x := by sorry
