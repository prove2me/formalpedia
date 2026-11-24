-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_hits_col
-- name    : Formalism.InvariantFactorPaths.G7.hits_col
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:30:14.226252+00:00
-- url     : https://prove2.me/theorems/6d386ca5-26e8-49e4-b3d8-ff2f9ad7fd34
-- title:
--   G7: hits col
-- statement:
--   The G7 construction uses the hits col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L671-L685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L671-L685

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
variable {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ)
  (ξ : κ → Fin r0 → K) (col : κ → Fin r1)

theorem Formalism.InvariantFactorPaths.G7.hits_col (S : Finset κ) (J : Finset (Fin r1)) (hS : ∀ k ∈ S, pos k = s → col k ∈ J)
    (β : κ →₀ ℕ) (hβ : ((univ.image I) ∩ J).card < ∑ k ∈ S, β k) :
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (minorAt s T I) = 0 := by sorry
