-- Prove2me | Theorems.Thm_Formalism_NG_detTri
-- name    : Formalism.NG.detTri
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:29.42446+00:00
-- url     : https://prove2.me/theorems/6535e6fb-9c0c-4b57-a6fb-0140e9321894
-- title:
--   NG: det Tri
-- statement:
--   The NG construction uses the det Tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/DetTri.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/DetTri.lean#L9-L41

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.detTri : StatDetTri := by sorry
