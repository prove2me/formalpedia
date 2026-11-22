-- Prove2me | Theorems.Thm_Formalism_YangianSpanCharacter_P_comm_of_inv
-- name    : Formalism.YangianSpanCharacter.P.comm_of_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:42:45.282466+00:00
-- url     : https://prove2.me/theorems/fd1fff2c-e3ba-4bfb-99ce-7c4a085ba697
-- title:
--   P: comm of inv
-- statement:
--   The P construction uses the comm of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L11-L15

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

theorem Formalism.YangianSpanCharacter.P.comm_of_inv {a b bi : A} (h1 : b * bi = 1) (h2 : bi * b = 1) (hab : a * b = b * a) :
    a * bi = bi * a := by sorry
