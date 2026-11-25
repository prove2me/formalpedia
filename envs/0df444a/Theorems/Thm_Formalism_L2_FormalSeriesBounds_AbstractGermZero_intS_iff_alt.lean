-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_intS_iff_alt
-- name    : Formalism.L2.FormalSeriesBounds.AbstractGermZero.intS_iff_alt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:12.381916+00:00
-- url     : https://prove2.me/theorems/a37e8bc8-e180-4a83-ac36-fc3398f3d6df
-- title:
--   Abstract Germ Zero: int S iff alt
-- statement:
--   The Abstract Germ Zero construction uses the int S iff alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AbstractGermZeroCondition.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AbstractGermZeroCondition.lean#L28-L30

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.AbstractGermZero
open Formalism.IncomingBounds
variable {C : Type} [Field C] (V : VF C)

theorem Formalism.L2.FormalSeriesBounds.AbstractGermZero.intS_iff_alt {σ : Type} (F : MvPowerSeries σ C) : IntS V F ↔ AltInv.IntS V.v F := by sorry
