-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_rayleigh_eq_sum_eigenvalues
-- name    : BookProof.SirkFinitePrecision.rayleigh_eq_sum_eigenvalues
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:05:34.258969+00:00
-- url     : https://prove2.me/theorems/719b2a83-0a11-41ca-a4d1-19d399fb183a
-- title:
--   The Rayleigh quotient is the eigenvalue-weighted sum of the squared coordinates
-- statement:
--   The Rayleigh quotient is the eigenvalue-weighted sum of the squared
--   coordinates.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.rayleigh_eq_sum_eigenvalues` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 98–114.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L98-L114

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.rayleigh_eq_sum_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.rayleigh_eq_sum_eigenvalues {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    rayleigh T x = ∑ i, hT.eigenvalues hn i * ‖coeff hT hn x i‖ ^ 2 := by sorry
