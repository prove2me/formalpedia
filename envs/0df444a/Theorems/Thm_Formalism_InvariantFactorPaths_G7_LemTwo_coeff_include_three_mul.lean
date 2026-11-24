-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_include_three_mul
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.coeff_include_three_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:23.709003+00:00
-- url     : https://prove2.me/theorems/e3389811-f0a5-408a-84a8-0f55b70153af
-- title:
--   Lem Two: coeff include three mul
-- statement:
--   The Lem Two construction uses the coeff include three mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L54-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L54-L84

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

theorem Formalism.InvariantFactorPaths.G7.LemTwo.coeff_include_three_mul (g : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m j : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (in3 g * MvPowerSeries.X 2 ^ j) =
      if j = m then MvPowerSeries.coeff e g else 0 := by sorry
