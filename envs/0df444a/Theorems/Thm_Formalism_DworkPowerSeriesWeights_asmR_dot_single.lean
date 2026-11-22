-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_single
-- name    : Formalism.DworkPowerSeriesWeights.asmR_dot_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:17.788843+00:00
-- url     : https://prove2.me/theorems/14317199-bb2c-415e-a05c-1a0481265101
-- title:
--   Dwork Power Series Weights: asm R dot single
-- statement:
--   The Dwork Power Series Weights construction uses the asm R dot single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L12-L15

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

theorem Formalism.DworkPowerSeriesWeights.asmR_dot_single {ι : Type v} (i : ι) (k : ℕ) (r : ι → ℝ) :
    dot (Finsupp.single i k) r = (k : ℝ) * r i := by sorry
