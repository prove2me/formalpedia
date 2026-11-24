-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_pair_sum
-- name    : Formalism.DworkPowerSeriesWeights.pair_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:58.188186+00:00
-- url     : https://prove2.me/theorems/c4fbabbd-778f-4e40-b228-711c762f0566
-- title:
--   Dwork Power Series Weights: pair sum
-- statement:
--   The Dwork Power Series Weights construction uses the pair sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L264-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L264-L288

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

theorem Formalism.DworkPowerSeriesWeights.pair_sum {K : Type u} [Field K] {R' : Type*} [CommSemiring R'] {n : Type} [Fintype n]
    [DecidableEq n] (c : K →+* R') (Mf Mt : Matrix n n K) (h : Mf * Mt.transpose = 1)
    (Y Y' : n → R') :
    (∑ a, (∑ i, c (Mf i a) * Y i) * (∑ i, c (Mt i a) * Y' i)) = ∑ i, Y i * Y' i := by sorry
