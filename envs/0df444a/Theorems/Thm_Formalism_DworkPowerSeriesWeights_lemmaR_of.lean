-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaR_of
-- name    : Formalism.DworkPowerSeriesWeights.lemmaR_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:25:26.658426+00:00
-- url     : https://prove2.me/theorems/f96e9a22-0d89-48c6-b4dc-a20a02b8fe3f
-- title:
--   Dwork Power Series Weights: lemma R of
-- statement:
--   The Dwork Power Series Weights construction uses the lemma R of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L72-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L72-L178

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.lemmaR_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v}) (hF : FactVal.{u, v})
    (hP : PureCross.{u, v}) : LemmaR.{u, v} := by sorry
