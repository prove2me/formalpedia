-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_law_integral
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLaws.law_integral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:53.783562+00:00
-- url     : https://prove2.me/theorems/adb21a36-65d5-4783-9c5f-be60e6d97484
-- title:
--   Formal Group Laws: law integral
-- statement:
--   The Formal Group Laws construction uses the law integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L275-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L275-L300

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

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLaws.law_integral {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (F : MvPowerSeries (Fin 2) K)
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hF : cob F (lgF K p) = 0) : Integral F := by sorry
