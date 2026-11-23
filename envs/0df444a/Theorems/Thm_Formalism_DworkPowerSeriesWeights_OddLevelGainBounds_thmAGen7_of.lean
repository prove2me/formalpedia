-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_thmAGen7_of
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAGen7_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:53.851721+00:00
-- url     : https://prove2.me/theorems/73720e56-9fd7-4648-a66a-57440136a391
-- title:
--   Odd Level Gain Bounds: thm AGen7 of
-- statement:
--   The Odd Level Gain Bounds construction uses the thm AGen7 of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/ThmAGen7Of.lean#L108-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/ThmAGen7Of.lean#L108-L154

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGen7Of
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
open Formalism.IncomingBounds MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAGen7_of (hO : ThmAOp7.{u}) : ThmAGen7.{u} := by sorry
