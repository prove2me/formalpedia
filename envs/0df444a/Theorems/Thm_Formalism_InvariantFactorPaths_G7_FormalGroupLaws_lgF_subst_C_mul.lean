-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_C_mul
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLaws.lgF_subst_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:24.957326+00:00
-- url     : https://prove2.me/theorems/467395a5-2f1f-4d64-a40b-cee919fa060f
-- title:
--   Formal Group Laws: lg F subst C mul
-- statement:
--   The Formal Group Laws construction uses the lg F subst C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L172-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L172-L183

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

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLaws.lgF_subst_C_mul {ι : Type} {ζ : K} {p : ℕ} (hζ : ζ ^ (p ^ 2 - 1) = 1) (hp : 2 ≤ p)
    (G : MvPowerSeries ι K) (hG : MvPowerSeries.constantCoeff G = 0) :
    PowerSeries.subst (MvPowerSeries.C ζ * G) (lgF K p) =
      MvPowerSeries.C ζ * PowerSeries.subst G (lgF K p) := by sorry
