-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_aff_sub
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.aff_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:09.440732+00:00
-- url     : https://prove2.me/theorems/37ff0b90-0266-4535-a4b7-6e758ce0f7c8
-- title:
--   Row Tie PSplit: aff sub
-- statement:
--   The Row Tie PSplit construction uses the aff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L13-L21

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.aff_sub (α β : K) (h : α ≠ 0 ∨ β ≠ 0) : {t : ℕ | α + (t : K) * β = 0}.Subsingleton := by sorry
