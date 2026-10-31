-- Prove2me | Theorems.Thm_BookProof_ChapterUnboundedPosition_adjoint_eq_mulOp
-- name    : BookProof.ChapterUnboundedPosition.adjoint_eq_mulOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:46:46.428039+00:00
-- url     : https://prove2.me/theorems/47358d0a-0170-49ea-ba66-8c97934187b7
-- title:
--   The Lean 4 theorem `adjoint_eq_mulOp` in the `ChapterUnboundedPosition` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `adjoint_eq_mulOp` in the `ChapterUnboundedPosition` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.adjoint_eq_mulOp
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

theorem BookProof.ChapterUnboundedPosition.adjoint_eq_mulOp (f : ℤ → ℝ) {phi eta : L2Z} (hphi : phi ∈ mulDomain f)
    (h : ∀ psi : mulDomain f, ⟪mulOp f psi, phi⟫_ℂ = ⟪(psi : L2Z), eta⟫_ℂ) :
    eta = mulOp f ⟨phi, hphi⟩ := by sorry
