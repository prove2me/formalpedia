-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_shift
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:13.950796+00:00
-- url     : https://prove2.me/theorems/4d9bca4c-d57f-4f45-82e1-b3ad76753715
-- title:
--   Hermitian Lattices Theory: theta Summable shift
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L78-L87

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

theorem Formalism.HermitianLatticesTheory.thetaSummable_shift (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (γ x : V) :
    Algebra.trace ℚ K (h x x) ≤
      2 * Algebra.trace ℚ K (h (γ + x) (γ + x)) + 2 * Algebra.trace ℚ K (h γ γ) := by sorry
