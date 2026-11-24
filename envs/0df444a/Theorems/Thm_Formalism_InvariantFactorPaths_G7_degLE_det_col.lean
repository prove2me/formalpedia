-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_det_col
-- name    : Formalism.InvariantFactorPaths.G7.degLE_det_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:03.621817+00:00
-- url     : https://prove2.me/theorems/035f545e-ed99-42d2-bf21-0f26d0dcde92
-- title:
--   G7: deg LE det col
-- statement:
--   The G7 construction uses the deg LE det col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L543-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L543-L551

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
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
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {κ R : Type} [CommRing R]

theorem Formalism.InvariantFactorPaths.G7.degLE_det_col {l : ℕ} {W : Finset κ} (N : Matrix (Fin l) (Fin l) (MvPolynomial κ R))
    (n : Fin l → ℕ) (h : ∀ i c, degLE W (n c) (N i c)) : degLE W (∑ c, n c) N.det := by sorry
