-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_integral_mul
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.integral_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:24.361891+00:00
-- url     : https://prove2.me/theorems/b093c1e4-66f3-4574-b41b-0581ffa54c65
-- title:
--   Lem Two: integral mul
-- statement:
--   The Lem Two construction uses the integral mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L171-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L171-L177

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
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
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.InvariantFactorPaths.G7.LemTwo.integral_mul {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f * g) := by sorry
