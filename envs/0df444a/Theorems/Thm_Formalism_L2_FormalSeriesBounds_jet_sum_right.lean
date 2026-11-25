-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_sum_right
-- name    : Formalism.L2.FormalSeriesBounds.jet_sum_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:59:29.491032+00:00
-- url     : https://prove2.me/theorems/1acd2fa6-6827-575c-b21d-8e696136301a
-- title:
--   Formal Series Bounds: jet sum right
-- statement:
--   The Formal Series Bounds construction uses the jet sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L29-L32

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

theorem Formalism.L2.FormalSeriesBounds.jet_sum_right {ι : Type} (s : Finset ι) (P : MvPolynomial σ C)
    (G : ι → MvPowerSeries σ C) : jetAt0 P (∑ j ∈ s, G j) = ∑ j ∈ s, jetAt0 P (G j) := by sorry
