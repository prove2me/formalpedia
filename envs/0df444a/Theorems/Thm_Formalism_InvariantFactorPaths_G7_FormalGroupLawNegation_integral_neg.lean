-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLawNegation_integral_neg
-- name    : Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation.integral_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:39.874252+00:00
-- url     : https://prove2.me/theorems/ec0e17f4-b6eb-4b5e-a547-a3a2e1d5e9f5
-- title:
--   Formal Group Law Negation: integral neg
-- statement:
--   The Formal Group Law Negation construction uses the integral neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/KOneConsequenceOf.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/KOneConsequenceOf.lean#L25-L29

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_KOneConsequenceOf
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
open Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation
open FormalGroupLaws

theorem Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation.integral_neg {K ι : Type} [NormedField K] {f : MvPowerSeries ι K} (hf : Integral f) :
    Integral (-f) := by sorry
