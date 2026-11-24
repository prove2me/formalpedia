-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_iff_sub
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.simeq_iff_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:03.815912+00:00
-- url     : https://prove2.me/theorems/69eec64d-edbc-4771-9ddf-02f6f13a4fb3
-- title:
--   Two Variable Swap Lemmas: simeq iff sub
-- statement:
--   The Two Variable Swap Lemmas construction uses the simeq iff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L229-L231

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
open MvPowerSeries
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.simeq_iff_sub {ι : Type} (f g : MvPowerSeries ι K) : Simeq f g ↔ Simeq (f - g) 0 := by sorry
