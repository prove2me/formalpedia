-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_smul
-- name    : Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:15.198452+00:00
-- url     : https://prove2.me/theorems/96913f8e-682e-42c0-800a-758fba5f1e94
-- title:
--   G7: coeff frob Var smul
-- statement:
--   The G7 construction uses the coeff frob Var smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L19-L21

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

theorem Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries ι K)
    (m : ι →₀ ℕ) : MvPowerSeries.coeff (p • m) (frobVar p f) = MvPowerSeries.coeff m f := by sorry
