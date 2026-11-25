-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_exists_jj
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.exists_jj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:43.797073+00:00
-- url     : https://prove2.me/theorems/de5340a0-2464-4b5a-8a23-293627ef0b34
-- title:
--   Pl: exists jj
-- statement:
--   The Pl construction uses the exists jj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/DetNeZeroOfChars.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/DetNeZeroOfChars.lean#L84-L88

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.exists_jj (d : ℕ) [NeZero d] : ∃ jj : ZMod d ≃ Fin d, ∀ a, jj (a + 1) = jj a + 1 := by sorry
