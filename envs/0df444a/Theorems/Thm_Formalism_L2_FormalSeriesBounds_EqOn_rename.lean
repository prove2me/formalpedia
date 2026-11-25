-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_rename
-- name    : Formalism.L2.FormalSeriesBounds.EqOn.rename
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:53.309172+00:00
-- url     : https://prove2.me/theorems/156f3d8c-c160-4d0c-857d-1b8e6e45dede
-- title:
--   Eq On: rename
-- statement:
--   The Eq On construction uses the rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L60-L71

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
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
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.EqOn.rename {τ : Type} (e : σ ↪ τ) {A : Set τ} {F G : MvPowerSeries σ K}
    (h : ∀ μ : σ →₀ ℕ, (∀ x ∈ μ.support, e x ∈ A) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G) :
    EqOn A (MvPowerSeries.rename e F) (MvPowerSeries.rename e G) := by sorry
