-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_subst
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLaws.subst_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:14.716812+00:00
-- url     : https://prove2.me/theorems/2e4a3fe8-0e6b-485d-bad2-e07df1eff122
-- title:
--   Formal Group Laws: subst subst
-- statement:
--   The Formal Group Laws construction uses the subst subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L140-L145

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

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLaws.subst_subst {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    MvPowerSeries.subst b (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.subst b a) f := by sorry
