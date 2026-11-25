-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_gauss_a_two_generic_of_entry
-- name    : Formalism.InvariantFactorPaths.G7.gauss_a_two_generic_of_entry
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:52.520243+00:00
-- url     : https://prove2.me/theorems/0df46957-e8e4-5f88-8e86-38434644afec
-- title:
--   G7: gauss a two generic of entry
-- statement:
--   The G7 construction uses the gauss a two generic of entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean#L158-L164

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open EGaussK DeterminantJetScaling ScaledSeriesSubstitution

theorem Formalism.InvariantFactorPaths.G7.gauss_a_two_generic_of_entry (hE : EntryCappedBound) : GaussBoundArbitraryGeneric := by sorry
