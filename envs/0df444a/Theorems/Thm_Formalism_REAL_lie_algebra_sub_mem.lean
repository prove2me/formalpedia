-- Prove2me | Theorems.Thm_Formalism_REAL_lie_algebra_sub_mem
-- name    : Formalism.REAL.lie_algebra_sub_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:26.215269+00:00
-- url     : https://prove2.me/theorems/1c2dc40e-8a04-4978-86f7-0af6e22ac753
-- title:
--   REAL: lie algebra sub mem
-- statement:
--   The REAL construction uses the lie algebra sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L86-L88

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

theorem Formalism.REAL.lie_algebra_sub_mem {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A - B) := by sorry
