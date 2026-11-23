-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_of_not_dvd
-- name    : Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:39.262482+00:00
-- url     : https://prove2.me/theorems/66075145-258e-42d2-ab03-e06532050436
-- title:
--   G7: coeff frob Var of not dvd
-- statement:
--   The G7 construction uses the coeff frob Var of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L23-L26

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
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

theorem Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0)
    (f : MvPowerSeries ι K) {n : ι →₀ ℕ} {i : ι} (h : ¬ p ∣ n i) :
    MvPowerSeries.coeff n (frobVar p f) = 0 := by sorry
