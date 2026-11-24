-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_ThmAJetA_of
-- name    : Formalism.DworkPowerSeriesWeights.ThmAJetA_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:04.243025+00:00
-- url     : https://prove2.me/theorems/e30ab064-0c7d-4d7c-913f-26e41f2e68ff
-- title:
--   Dwork Power Series Weights: Thm AJet A of
-- statement:
--   The Dwork Power Series Weights construction uses the Thm AJet A of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAOneMonomialLogLoss.lean#L15-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAOneMonomialLogLoss.lean#L15-L236

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.ThmAJetA_of (hS : LemmaS.{u}) (hR : LemmaRA.{u, 0}) (hA : ThmAAssembly)
    (hFP : FramePure.{u}) : ThmAJetA.{u} := by sorry
