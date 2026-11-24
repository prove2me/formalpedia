-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_pairExp_apply
-- name    : Formalism.DworkPowerSeriesWeights.pairExp_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:55.374376+00:00
-- url     : https://prove2.me/theorems/ab6592a3-7b8c-45c5-a9c6-94977dbdffe1
-- title:
--   Dwork Power Series Weights: pair Exp apply
-- statement:
--   The Dwork Power Series Weights construction uses the pair Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L27-L36

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
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

theorem Formalism.DworkPowerSeriesWeights.pairExp_apply {ι : Type} [Fintype ι] (n : ι → ℕ) (b : Bool) (i : ι) :
    pairExp n (b, i) = n i := by sorry
