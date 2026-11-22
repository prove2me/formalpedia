-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_nonneg
-- name    : Formalism.DworkPowerSeriesWeights.asmR_dot_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:21.056802+00:00
-- url     : https://prove2.me/theorems/f27b4f57-2c99-4cc4-863b-3b8bdd08f67a
-- title:
--   Dwork Power Series Weights: asm R dot nonneg
-- statement:
--   The Dwork Power Series Weights construction uses the asm R dot nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmRDotAddRight.lean#L36-L38

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

theorem Formalism.DworkPowerSeriesWeights.asmR_dot_nonneg {ι : Type v} (n : ι →₀ ℕ) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) : 0 ≤ dot n r := by sorry
