-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_least_odd_top_level_spec
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.least_odd_top_level_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:57.965954+00:00
-- url     : https://prove2.me/theorems/5142f2af-5c67-4d55-989d-57475e82a449
-- title:
--   Odd Level Gain Bounds: least odd top level spec
-- statement:
--   The Odd Level Gain Bounds construction uses the least odd top level spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CompanionTheory.lean#L156-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CompanionTheory.lean#L156-L192

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.least_odd_top_level_spec {d : ℕ} [NeZero d] (TT : Finset (ZMod d)) (s : ZMod d) (e : ℕ)
    (h : dTop d TT s = (e : ℕ∞)) :
    (Odd e ∧ s + (e : ZMod d) ∈ TT) ∧ ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → e ≤ e' := by sorry
