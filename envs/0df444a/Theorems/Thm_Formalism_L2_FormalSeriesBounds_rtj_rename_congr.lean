-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_congr
-- name    : Formalism.L2.FormalSeriesBounds.rtj_rename_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:49.316643+00:00
-- url     : https://prove2.me/theorems/52238353-25db-4e5f-b75e-31d4e1bf805e
-- title:
--   Formal Series Bounds: rtj rename congr
-- statement:
--   The Formal Series Bounds construction uses the rtj rename congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L348-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L348-L351

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
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}

theorem Formalism.L2.FormalSeriesBounds.rtj_rename_congr {α β : Type} {f g : α → β} [Filter.TendstoCofinite f] [Filter.TendstoCofinite g]
    (h : f = g) (p : MvPowerSeries α C) : MvPowerSeries.rename f p = MvPowerSeries.rename g p := by sorry
