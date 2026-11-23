-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_inVar
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_inVar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:14.633493+00:00
-- url     : https://prove2.me/theorems/3d2de1a5-6fbd-43ba-92a1-09ad171a667d
-- title:
--   Formal Group Laws: map in Var
-- statement:
--   The Formal Group Laws construction uses the map in Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L67-L70

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_inVar {L ι : Type} [Field L] (φ : K →+* L) (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map φ (at1 x f) = at1 x (PowerSeries.map φ f) := by sorry
