-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_theorem_A_monomial_of_lemmas
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.theorem_A_monomial_of_lemmas
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:40.031822+00:00
-- url     : https://prove2.me/theorems/5af46d03-bc36-4a45-8202-9cea0c4fb841
-- title:
--   Odd Level Gain Bounds: theorem A monomial of lemmas
-- statement:
--   The Odd Level Gain Bounds construction uses the theorem A monomial of lemmas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/TheoremAMonomialOfLemmas.lean#L20-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/TheoremAMonomialOfLemmas.lean#L20-L238

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TheoremAMonomialOfLemmas
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
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.theorem_A_monomial_of_lemmas (hS : LemmaS.{u}) (hR : LemmaRA.{u, 0}) (hA : ThmAAssembly7)
    (hFP : FramePure.{u}) : ThmAJet7.{u} := by sorry
