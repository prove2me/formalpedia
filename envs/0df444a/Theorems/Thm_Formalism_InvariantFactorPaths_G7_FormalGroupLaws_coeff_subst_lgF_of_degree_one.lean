-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_subst_lgF_of_degree_one
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_subst_lgF_of_degree_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:13.825469+00:00
-- url     : https://prove2.me/theorems/c2b39293-0b06-42eb-a554-215cdb769562
-- title:
--   Formal Group Laws: coeff subst lg F of degree one
-- statement:
--   The Formal Group Laws construction uses the coeff subst lg F of degree one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L185-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean#L185-L214

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

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_subst_lgF_of_degree_one {ι : Type} (p : ℕ) (hp : 2 ≤ p) (F : MvPowerSeries ι K)
    (hF : MvPowerSeries.constantCoeff F = 0) (n : ι →₀ ℕ) (hn : n.degree = 1) :
    MvPowerSeries.coeff n (PowerSeries.subst F (lgF K p)) = MvPowerSeries.coeff n F := by sorry
