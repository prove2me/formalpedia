-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_commute_aeval
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.commute_aeval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:00.935576+00:00
-- url     : https://prove2.me/theorems/f8dc21e2-0aed-4017-a0a4-d66db2f8ba3a
-- title:
--   Row Tie PSplit: commute aeval
-- statement:
--   The Row Tie PSplit construction uses the commute aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L66-L76

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
variable {K : Type} [Field K] {n : ℕ}

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.commute_aeval {A B : Matrix (Fin n) (Fin n) K} (h : Commute A B) (f : K[X]) : Commute A (aeval B f) := by sorry
