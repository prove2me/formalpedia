-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_minorAt_one
-- name    : Formalism.InvariantFactorPaths.G7.EGauss.minorAt_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:58.995466+00:00
-- url     : https://prove2.me/theorems/344ae3da-ea90-4b12-b627-06110baf1ccb
-- title:
--   EGauss: minor At one
-- statement:
--   The EGauss construction uses the minor At one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L55-L62

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

theorem Formalism.InvariantFactorPaths.G7.EGauss.minorAt_one {σ : Type} (s : σ) {l : ℕ} (h : l = 1) (T : Fin l → Fin r0 → K)
    (I : Fin l → Fin r1) :
    minorAt s T I = ∑ a, MvPolynomial.C (T ⟨0, by omega⟩ a) *
      MvPolynomial.X (s, a, I ⟨0, by omega⟩) := by sorry
