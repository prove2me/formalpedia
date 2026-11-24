-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_prod
-- name    : Formalism.InvariantFactorPaths.G7.biHom_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:51.554032+00:00
-- url     : https://prove2.me/theorems/3d68150f-b9a1-4a03-9991-86085c039687
-- title:
--   G7: bi Hom prod
-- statement:
--   The G7 construction uses the bi Hom prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L310-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L310-L319

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

theorem Formalism.InvariantFactorPaths.G7.biHom_prod {α : Type*} (s : Finset α) (d : α → ℕ)
    (F : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, biHom (d a) (F a)) :
    biHom (∑ a ∈ s, d a) (∏ a ∈ s, F a) := by sorry
