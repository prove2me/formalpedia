-- Prove2me | Theorems.Thm_Formalism_REAL_mulRightCLM_apply
-- name    : Formalism.REAL.mulRightCLM_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:12.503598+00:00
-- url     : https://prove2.me/theorems/a9d31cb4-9a6a-4ed9-8855-329487bfc34c
-- title:
--   REAL: mul Right CLM apply
-- statement:
--   The REAL construction uses the mul Right CLM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L16-L16

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.mulRightCLM_apply {n : ℕ} (X h : Matrix (Fin n) (Fin n) ℂ) : mulRightRealCLM X h = h * X := by sorry
