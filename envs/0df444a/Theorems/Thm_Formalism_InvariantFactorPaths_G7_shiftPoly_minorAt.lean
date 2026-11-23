-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_minorAt
-- name    : Formalism.InvariantFactorPaths.G7.shiftPoly_minorAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:40.597804+00:00
-- url     : https://prove2.me/theorems/aa237cdd-7e06-4c63-9001-b776317239db
-- title:
--   G7: shift Poly minor At
-- statement:
--   The G7 construction uses the shift Poly minor At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L623-L633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L623-L633

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
variable {K σ κ : Type} [Field K] [DecidableEq σ] [Fintype κ]

theorem Formalism.InvariantFactorPaths.G7.shiftPoly_minorAt {r0 r1 l : ℕ} (b : κ → σ × Fin r0 × Fin r1 → K) (s : σ)
    (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) :
    shiftPoly b (minorAt s T I) = (Matrix.of fun (i c : Fin l) =>
      ∑ a, MvPolynomial.C (MvPolynomial.C (T i a)) * shiftGen b (s, a, I c)).det := by sorry
