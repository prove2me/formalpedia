-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_product
-- name    : Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_product
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:08.400212+00:00
-- url     : https://prove2.me/theorems/63ba0718-19f6-46ea-bffb-a5728db5806e
-- title:
--   Coboundary Series: partial coboundary product
-- statement:
--   The Coboundary Series construction uses the partial coboundary product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L88-L96

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
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
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_product {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (f g : PowerSeries K) : d1 F (at1 0 f * at1 1 g) = in3 (cob F f) * at1 2 g := by sorry
