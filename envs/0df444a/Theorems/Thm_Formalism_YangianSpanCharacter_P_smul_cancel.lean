-- Prove2me | Theorems.Thm_Formalism_YangianSpanCharacter_P_smul_cancel
-- name    : Formalism.YangianSpanCharacter.P.smul_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:24.284201+00:00
-- url     : https://prove2.me/theorems/b17a6e0f-3fee-4811-9887-18607053c50f
-- title:
--   P: smul cancel
-- statement:
--   The P construction uses the smul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L17-L20

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem Formalism.YangianSpanCharacter.P.smul_cancel {c : 𝕜} (hc : c ≠ 0) {x y : A} (h : c • x = c • y) : x = y := by sorry
