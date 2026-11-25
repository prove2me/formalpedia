-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_germ_sub
-- name    : Formalism.L2.FormalSeriesBounds.AbstractGermZero.germ_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:00.2243+00:00
-- url     : https://prove2.me/theorems/99eaa7a4-93c5-4758-9857-5fd2101c0e11
-- title:
--   Abstract Germ Zero: germ sub
-- statement:
--   The Abstract Germ Zero construction uses the germ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AbstractGermZeroCondition.lean#L211-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AbstractGermZeroCondition.lean#L211-L244

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

theorem Formalism.L2.FormalSeriesBounds.AbstractGermZero.germ_sub {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t t₂ h : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0₂ : ∀ g c, MvPowerSeries.constantCoeff (t₂ g c) = 0)
    (hh0 : ∀ g c, MvPowerSeries.constantCoeff (h g c) = 0) (hhI : ∀ g c, IntS V (h g c))
    (hth : ∀ g c, t g c = MvPowerSeries.subst (t₂ g) (h g c)) :
    IntGerm V t ⊆ IntGerm V t₂ := by sorry
