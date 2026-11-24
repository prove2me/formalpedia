-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_coeff_lg_lg_eq_zero
-- name    : Formalism.InvariantFactorPaths.G7.CoboundarySeries.coeff_lg_lg_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:05.14463+00:00
-- url     : https://prove2.me/theorems/bfefbb0a-6ce2-4f75-b955-fecb777fdc49
-- title:
--   Coboundary Series: coeff lg lg eq zero
-- statement:
--   The Coboundary Series construction uses the coeff lg lg eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L198-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L198-L213

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

theorem Formalism.InvariantFactorPaths.G7.CoboundarySeries.coeff_lg_lg_eq_zero {p : ℕ} (hp : 2 ≤ p) {n : Fin 2 →₀ ℕ}
    (hn : n 0 ≡ p * n 1 [MOD p ^ 2 - 1]) :
    coeff n (at1 0 (lgF K p) * at1 1 (lgF K p)) = 0 := by sorry
