-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_suppOK_Hser
-- name    : Formalism.InvariantFactorPaths.G7.CoboundarySeries.suppOK_Hser
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:58.982875+00:00
-- url     : https://prove2.me/theorems/fa8cbb67-03b8-4549-a72a-df6811368ea1
-- title:
--   Coboundary Series: supp OK Hser
-- statement:
--   The Coboundary Series construction uses the supp OK Hser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L192-L196

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

theorem Formalism.InvariantFactorPaths.G7.CoboundarySeries.suppOK_Hser {p : ℕ} (hp : 2 ≤ p) (σ : K →+* K) {G : MvPowerSeries (Fin 2) K}
    (hG : SuppOK p G) (γ γ' : K) : SuppOK p (Hser p σ G γ γ') := by sorry
