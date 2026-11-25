-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_subst_linS
-- name    : Formalism.L2.FormalSeriesBounds.jet_subst_linS
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:06.624005+00:00
-- url     : https://prove2.me/theorems/68ac6232-83fe-5fa6-818c-796c5eb84528
-- title:
--   Formal Series Bounds: jet subst lin S
-- statement:
--   The Formal Series Bounds construction uses the jet subst lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L96-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L96-L120

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}

theorem Formalism.L2.FormalSeriesBounds.jet_subst_linS [Fintype σ] [Fintype τ] (M : τ → σ → C) (Q : MvPolynomial τ C)
    (F : MvPowerSeries σ C) :
    jetAt0 Q (subst (linS M) F) = jetAt0 (linT M Q) F := by sorry
