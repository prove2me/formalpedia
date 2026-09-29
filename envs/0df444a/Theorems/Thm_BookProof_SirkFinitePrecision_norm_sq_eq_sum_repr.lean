-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_norm_sq_eq_sum_repr
-- name    : BookProof.SirkFinitePrecision.norm_sq_eq_sum_repr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:50:18.526617+00:00
-- url     : https://prove2.me/theorems/a24ed736-29ca-44a2-99c6-ebc9919da9d5
-- title:
--   Parseval's identity in the eigenbasis
-- statement:
--   Parseval's identity in the eigenbasis.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.norm_sq_eq_sum_repr` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 91–96.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L91-L96

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.norm_sq_eq_sum_repr
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.norm_sq_eq_sum_repr {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖coeff hT hn x i‖ ^ 2 := by sorry
