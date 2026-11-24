-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_eq_zero_of_div
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.eq_zero_of_div
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:07.913053+00:00
-- url     : https://prove2.me/theorems/135a3ad9-cbfc-4b37-8c86-89c617b9c13b
-- title:
--   Lem Two: eq zero of div
-- statement:
--   The Lem Two construction uses the eq zero of div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L257-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L257-L272

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

theorem Formalism.InvariantFactorPaths.G7.LemTwo.eq_zero_of_div {p : ℕ} (hp : 2 ≤ p) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x : K}
    (h : ∀ N : ℕ, ∃ i, N ≤ i ∧ ‖((p : K) ^ i)⁻¹ * x‖ ≤ 1) : x = 0 := by sorry
