-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_refl
-- name    : Formalism.L2.FormalSeriesBounds.EqOn.refl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:31:30.345038+00:00
-- url     : https://prove2.me/theorems/3d6b55d2-1c8f-4c0e-a0e4-060db66a5c89
-- title:
--   Eq On: refl
-- statement:
--   The Eq On construction uses the refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L20-L20

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

theorem Formalism.L2.FormalSeriesBounds.EqOn.refl (A : Set σ) (F : MvPowerSeries σ K) : EqOn A F F := by sorry
