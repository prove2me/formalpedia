-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_pderiv_shiftGen
-- name    : Formalism.InvariantFactorPaths.G7.pderiv_shiftGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:34.883732+00:00
-- url     : https://prove2.me/theorems/d81de880-bcd9-48af-9506-77faabd4840b
-- title:
--   G7: pderiv shift Gen
-- statement:
--   The G7 construction uses the pderiv shift Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L76-L85

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
variable {K ι κ : Type} [Field K] [Fintype κ]

theorem Formalism.InvariantFactorPaths.G7.pderiv_shiftGen (b : κ → ι → K) (x : ι) (k : κ) :
    MvPolynomial.pderiv k (shiftGen b x) = MvPolynomial.C (MvPolynomial.C (b k x)) := by sorry
