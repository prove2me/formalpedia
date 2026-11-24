-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_monomial_left
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_monomial_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:34.556259+00:00
-- url     : https://prove2.me/theorems/1188c749-8c4d-4844-ad1e-b058a083a6fa
-- title:
--   Dwork Power Series Weights: jet Pair monomial left
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair monomial left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L203-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L203-L208

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.jetPair_monomial_left {K : Type u} [Field K] {ι : Type} (κ : ι →₀ ℕ)
    (F : MvPowerSeries ι K) :
    jetPair (monomial κ (1 : K)) F = ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by sorry
