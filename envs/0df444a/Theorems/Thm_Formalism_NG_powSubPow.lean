-- Prove2me | Theorems.Thm_Formalism_NG_powSubPow
-- name    : Formalism.NG.powSubPow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:50.653354+00:00
-- url     : https://prove2.me/theorems/2aee2f84-a2cf-4e2b-b31d-183cd3690492
-- title:
--   NG: pow Sub Pow
-- statement:
--   The NG construction uses the pow Sub Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ProdEraseZero.lean#L13-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ProdEraseZero.lean#L13-L52

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ProdEraseZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.NG

theorem Formalism.NG.powSubPow : StatPowSubPow := by sorry
