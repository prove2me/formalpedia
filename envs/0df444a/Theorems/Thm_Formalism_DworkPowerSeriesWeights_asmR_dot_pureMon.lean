-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_pureMon
-- name    : Formalism.DworkPowerSeriesWeights.asmR_dot_pureMon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:58.344902+00:00
-- url     : https://prove2.me/theorems/cd676f59-bac6-4422-bf6d-5d6053c75f26
-- title:
--   Dwork Power Series Weights: asm R dot pure Mon
-- statement:
--   The Dwork Power Series Weights construction uses the asm R dot pure Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L17-L23

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
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

theorem Formalism.DworkPowerSeriesWeights.asmR_dot_pureMon {ι : Type v} [DecidableEq ι] (l : ℕ) (i j : ι) (α β : ℕ) (r : ι → ℝ) :
    dot (pureMon l i j α β) r = (l : ℝ) ^ α * r i + (l : ℝ) ^ β * r j := by sorry
