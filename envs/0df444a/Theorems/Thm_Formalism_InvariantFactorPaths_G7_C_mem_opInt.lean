-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_C_mem_opInt
-- name    : Formalism.InvariantFactorPaths.G7.C_mem_opInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:39.984304+00:00
-- url     : https://prove2.me/theorems/09f5105f-33ec-43b2-ace9-b2b749648797
-- title:
--   G7: C mem op Int
-- statement:
--   The G7 construction uses the C mem op Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L419-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L419-L426

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
variable (K ι κ : Type) [NormedField K] [IsUltrametricDist K]
variable {K ι κ}

theorem Formalism.InvariantFactorPaths.G7.C_mem_opInt {c : K} (hc : ‖c‖ ≤ 1) :
    (MvPolynomial.C c : MvPolynomial ι K) ∈ Formalism.DworkPowerSeriesWeights.opInt K ι := by sorry
