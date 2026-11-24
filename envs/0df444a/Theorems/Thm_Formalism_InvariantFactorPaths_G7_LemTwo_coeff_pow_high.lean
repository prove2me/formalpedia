-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_pow_high
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.coeff_pow_high
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:58.986813+00:00
-- url     : https://prove2.me/theorems/b35e3be7-cf47-4674-9521-b691c463763d
-- title:
--   Lem Two: coeff pow high
-- statement:
--   The Lem Two construction uses the coeff pow high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L102-L105

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
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.LemTwo.coeff_pow_high {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0)
    {e : ι →₀ ℕ} {k : ℕ} (hk : e.degree < k) : MvPowerSeries.coeff e (f ^ k) = 0 := by sorry
