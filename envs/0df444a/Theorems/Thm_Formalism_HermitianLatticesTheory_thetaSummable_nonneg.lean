-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_nonneg
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:17.450891+00:00
-- url     : https://prove2.me/theorems/bcaa5e59-740c-4bf4-b281-2d751b6eab78
-- title:
--   Hermitian Lattices Theory: theta Summable nonneg
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L70-L76

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLatticesTheory.thetaSummable_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (x : V) :
    0 ≤ Algebra.trace ℚ K (h x x) := by sorry
