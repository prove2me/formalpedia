-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_mvExp
-- name    : Formalism.L2.FormalSeriesBounds.rtj_rename_mvExp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:34.606264+00:00
-- url     : https://prove2.me/theorems/7becb8cc-1b97-4325-9c78-9cf56303a0b9
-- title:
--   Formal Series Bounds: rtj rename mv Exp
-- statement:
--   The Formal Series Bounds construction uses the rtj rename mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L282-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L282-L300

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ τ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_rename_mvExp (e : σ ↪ τ) (L : MvPowerSeries σ K) :
    MvPowerSeries.rename e (mvExp L) = mvExp (MvPowerSeries.rename e L) := by sorry
