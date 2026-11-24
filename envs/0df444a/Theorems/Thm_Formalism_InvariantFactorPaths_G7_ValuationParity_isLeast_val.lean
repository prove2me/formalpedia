-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_isLeast_val
-- name    : Formalism.InvariantFactorPaths.G7.ValuationParity.isLeast_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:04.166168+00:00
-- url     : https://prove2.me/theorems/5d4cec2b-0541-41b1-91f2-4dc3661f9f37
-- title:
--   Valuation Parity: is Least val
-- statement:
--   The Valuation Parity construction uses the is Least val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L47-L53

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ValuationParity

theorem Formalism.InvariantFactorPaths.G7.ValuationParity.isLeast_val {n : ℕ} [NeZero n] (s s' : ZMod n) (h : 1 ≤ (s' - s).val) :
    IsLeast {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} (s' - s).val := by sorry
