-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_sum_sub_sigma
-- name    : Formalism.InvariantFactorPaths.G7.EGauss.sum_sub_sigma
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:39.598347+00:00
-- url     : https://prove2.me/theorems/6b9af651-80f2-4604-9f40-50de211e78a8
-- title:
--   EGauss: sum sub sigma
-- statement:
--   The EGauss construction uses the sum sub sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L94-L103

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGauss
variable {K : Type} [Field K] {ν r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.EGauss.sum_sub_sigma {S : Type} [Fintype S] [DecidableEq S] (colN : S → ℕ)
    (P : (Σ s, Fin (colN s)) → Prop) [DecidablePred P] (f : (Σ s, Fin (colN s)) → ℕ) (s : S) :
    ∑ x : {x // P x}, (if x.1.1 = s then f x.1 else 0) =
      ∑ c : Fin (colN s), if P ⟨s, c⟩ then f ⟨s, c⟩ else 0 := by sorry
