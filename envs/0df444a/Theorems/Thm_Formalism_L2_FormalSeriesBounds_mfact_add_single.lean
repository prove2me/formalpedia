-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_mfact_add_single
-- name    : Formalism.L2.FormalSeriesBounds.mfact_add_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:59:13.09686+00:00
-- url     : https://prove2.me/theorems/4b662877-a895-5b6e-bbbf-5118b5ec35d6
-- title:
--   Formal Series Bounds: mfact add single
-- statement:
--   The Formal Series Bounds construction uses the mfact add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L41-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L41-L62

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

theorem Formalism.L2.FormalSeriesBounds.mfact_add_single (m : σ →₀ ℕ) (x : σ) :
    mfact (m + Finsupp.single x 1) = (m x + 1) * mfact m := by sorry
