-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_add_right
-- name    : Formalism.L2.FormalSeriesBounds.jet_add_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:01.447066+00:00
-- url     : https://prove2.me/theorems/b126bbdf-3acb-57c8-94d6-14394d7435f5
-- title:
--   Formal Series Bounds: jet add right
-- statement:
--   The Formal Series Bounds construction uses the jet add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L17-L19

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

theorem Formalism.L2.FormalSeriesBounds.jet_add_right (P : MvPolynomial σ C) (G H : MvPowerSeries σ C) :
    jetAt0 P (G + H) = jetAt0 P G + jetAt0 P H := by sorry
