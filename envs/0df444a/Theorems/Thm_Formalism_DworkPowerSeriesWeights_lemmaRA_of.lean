-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaRA_of
-- name    : Formalism.DworkPowerSeriesWeights.lemmaRA_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:55.09836+00:00
-- url     : https://prove2.me/theorems/17ab47ca-42e6-4219-bc39-18f32bc68187
-- title:
--   Dwork Power Series Weights: lemma RA of
-- statement:
--   The Dwork Power Series Weights construction uses the lemma RA of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LemmaRA.lean#L55-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LemmaRA.lean#L55-L168

import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
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

theorem Formalism.DworkPowerSeriesWeights.lemmaRA_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v})
    (hP : PureCross.{u, v}) : LemmaRA.{u, v} := by sorry
