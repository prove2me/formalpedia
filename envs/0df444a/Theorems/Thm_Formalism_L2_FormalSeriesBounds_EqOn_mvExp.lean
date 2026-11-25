-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
-- name    : Formalism.L2.FormalSeriesBounds.EqOn.mvExp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:52.072262+00:00
-- url     : https://prove2.me/theorems/bb3aa916-2e23-42e2-91bc-e1322eaae61d
-- title:
--   Eq On: mv Exp
-- statement:
--   The Eq On construction uses the mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L49-L53

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

theorem Formalism.L2.FormalSeriesBounds.EqOn.mvExp {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) : EqOn A (mvExp F) (mvExp G) := by sorry
