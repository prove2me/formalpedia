-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_jetAt0_one
-- name    : Formalism.L2.FormalSeriesBounds.RF.jetAt0_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:55.22079+00:00
-- url     : https://prove2.me/theorems/d2da1634-cc17-4656-ae4e-ab06c84e3c26
-- title:
--   RF: jet At0 one
-- statement:
--   The RF construction uses the jet At0 one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L21-L24

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.RF.jetAt0_one (G : MvPowerSeries σ C) : jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by sorry
