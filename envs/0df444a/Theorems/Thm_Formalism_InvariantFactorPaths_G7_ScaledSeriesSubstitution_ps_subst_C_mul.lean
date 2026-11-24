-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_ps_subst_C_mul
-- name    : Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.ps_subst_C_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:31.614499+00:00
-- url     : https://prove2.me/theorems/09fb4cef-4f3e-4cd0-b625-ac51ee2f2381
-- title:
--   Scaled Series Substitution: ps subst C mul
-- statement:
--   The Scaled Series Substitution construction uses the ps subst C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EChain.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EChain.lean#L61-L64

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution

theorem Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.ps_subst_C_mul {K κ : Type} [Field K] {w : MvPowerSeries κ K}
    (hw : PowerSeries.HasSubst w) (a : K) (f : PowerSeries K) :
    PowerSeries.subst w (PowerSeries.C a * f) = MvPowerSeries.C a * PowerSeries.subst w f := by sorry
