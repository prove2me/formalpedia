-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_mulOp_adjoint_apply
-- name    : BookProof.ChapterUnboundedPosition.mulOp_adjoint_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:46:25.485336+00:00
-- url     : https://prove2.me/theorems/af42d25c-e6cf-4c2e-9297-f78ca3a3952c
-- title:
--   The Lean 4 theorem `mulOp_adjoint_apply` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulOp_adjoint_apply` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.mulOp_adjoint_apply
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterF7
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem BookProof.ChapterUnboundedPosition.mulOp_adjoint_apply (f : ℤ → ℝ) {phi eta : L2Z}
    (h : ∀ psi : mulDomain f, ⟪mulOp f psi, phi⟫_ℂ = ⟪(psi : L2Z), eta⟫_ℂ) :
    (∀ k, (f k : ℂ) * (phi : ℤ → ℂ) k = (eta : ℤ → ℂ) k) ∧ phi ∈ mulDomain f := by sorry
