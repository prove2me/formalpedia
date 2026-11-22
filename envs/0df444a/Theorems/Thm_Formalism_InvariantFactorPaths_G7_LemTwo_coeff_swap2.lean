-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_swap2
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.coeff_swap2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:05.698263+00:00
-- url     : https://prove2.me/theorems/8760b363-f790-4b0c-bda4-bc641bde0c96
-- title:
--   Lem Two: coeff swap2
-- statement:
--   The Lem Two construction uses the coeff swap2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L211-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L211-L220

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

theorem Formalism.InvariantFactorPaths.G7.LemTwo.coeff_swap2 (H : MvPowerSeries (Fin 2) K) (i k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (swap2 H) =
      MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 i) H := by sorry
