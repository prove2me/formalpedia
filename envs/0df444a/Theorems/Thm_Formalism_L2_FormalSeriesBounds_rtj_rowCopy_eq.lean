-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rowCopy_eq
-- name    : Formalism.L2.FormalSeriesBounds.rtj_rowCopy_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:21.4958+00:00
-- url     : https://prove2.me/theorems/aac5bf98-0801-46d0-83ea-b9468173d04d
-- title:
--   Formal Series Bounds: rtj row Copy eq
-- statement:
--   The Formal Series Bounds construction uses the rtj row Copy eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L342-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L342-L346

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

theorem Formalism.L2.FormalSeriesBounds.rtj_rowCopy_eq {M : ℕ} (ρ : Fin M) (F : MvPowerSeries (WV I) C) :
    rowCopy ρ F = MvPowerSeries.rename (rtjR ρ) F := by sorry
