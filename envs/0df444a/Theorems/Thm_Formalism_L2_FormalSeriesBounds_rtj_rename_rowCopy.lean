-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_rowCopy
-- name    : Formalism.L2.FormalSeriesBounds.rtj_rename_rowCopy
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:37.527746+00:00
-- url     : https://prove2.me/theorems/8e5b7d07-d7d4-4dd2-ba93-120e931f1cd0
-- title:
--   Formal Series Bounds: rtj rename row Copy
-- statement:
--   The Formal Series Bounds construction uses the rtj rename row Copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L353-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L353-L359

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

theorem Formalism.L2.FormalSeriesBounds.rtj_rename_rowCopy {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (i : Fin K) (ρ : Fin (what₂ i)) (F : MvPowerSeries (WV I) C) :
    MvPowerSeries.rename (rtjE hpl i) (rowCopy ρ F) = rowCopy (pl ⟨i, ρ⟩) F := by sorry
