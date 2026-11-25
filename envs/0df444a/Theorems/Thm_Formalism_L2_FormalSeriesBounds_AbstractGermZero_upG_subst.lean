-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_upG_subst
-- name    : Formalism.L2.FormalSeriesBounds.AbstractGermZero.upG_subst
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:38.783021+00:00
-- url     : https://prove2.me/theorems/3b3e920c-2feb-40b6-aa6c-ea459b1c491a
-- title:
--   Abstract Germ Zero: up G subst
-- statement:
--   The Abstract Germ Zero construction uses the up G subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AbstractGermZeroCondition.lean#L189-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AbstractGermZeroCondition.lean#L189-L209

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

theorem Formalism.L2.FormalSeriesBounds.AbstractGermZero.upG_subst {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) (g : Fin 2) (γ : MvPowerSeries (I g) C) :
    MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) (upG g γ) = upG g (MvPowerSeries.subst (t g) γ) := by sorry
