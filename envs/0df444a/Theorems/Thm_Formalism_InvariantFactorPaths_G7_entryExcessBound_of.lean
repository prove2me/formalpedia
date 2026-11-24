-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_entryExcessBound_of
-- name    : Formalism.InvariantFactorPaths.G7.entryExcessBound_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:11.706966+00:00
-- url     : https://prove2.me/theorems/8729507a-7ac7-4686-9ff1-1d325412714d
-- title:
--   G7: entry Excess Bound of
-- statement:
--   The G7 construction uses the entry Excess Bound of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L177-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean#L177-L312

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
open ValuationParity

theorem Formalism.InvariantFactorPaths.G7.entryExcessBound_of (hS : EntryStar) (hC : HitsCapPos) (hA : ExcessGainBound) (hL : ChargeLemma) : EntryExcessBound := by sorry
