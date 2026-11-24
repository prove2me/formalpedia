-- Prove2me | Theorems.Thm_Formalism_REAL_right_derivative_zero_outside_support
-- name    : Formalism.REAL.right_derivative_zero_outside_support
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:41:37.416627+00:00
-- url     : https://prove2.me/theorems/922614f7-ae49-42a5-8c76-686921218714
-- title:
--   REAL: right derivative zero outside support
-- statement:
--   The REAL construction uses the right derivative zero outside support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/RightDerivativeZeroOutsideSupport.lean#L271-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/RightDerivativeZeroOutsideSupport.lean#L271-L288

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.right_derivative_zero_outside_support {n : ℕ} {ε : Fin n → Bool} {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {X h : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hX : inG ε X) (hh : inUJ ε h)
    (hsupp : ∀ g, inUJ ε g → R < hs g → φ g = 0) (hR : R < hs h) : Rd X φ h = 0 := by sorry
