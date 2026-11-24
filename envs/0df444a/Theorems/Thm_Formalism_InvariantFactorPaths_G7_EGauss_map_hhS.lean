-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_map_hhS
-- name    : Formalism.InvariantFactorPaths.G7.EGauss.map_hhS
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:53:40.989165+00:00
-- url     : https://prove2.me/theorems/1b1c0f34-6d02-4366-942a-8c9faf78fee5
-- title:
--   EGauss: map hh S
-- statement:
--   The EGauss construction uses the map hh S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean#L33-L36

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
variable {F K : Type} [NormedField F] [NormedField K] (φ : F →+* K) {ν r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.EGauss.map_hhS [NeZero ν] (p : ℕ) (u : ZMod (2 * ν) → F) :
    MvPowerSeries.map φ (hhS (r0 := r0) (r1 := r1) p u) = hhS p (fun s => φ (u s)) := by sorry
