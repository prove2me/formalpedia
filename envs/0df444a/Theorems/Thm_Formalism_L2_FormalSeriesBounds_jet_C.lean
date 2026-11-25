-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_C
-- name    : Formalism.L2.FormalSeriesBounds.jet_C
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:02:48.270168+00:00
-- url     : https://prove2.me/theorems/9cf33742-def9-4c7b-ac03-8b0685e63a83
-- title:
--   Formal Series Bounds: jet C
-- statement:
--   The Formal Series Bounds construction uses the jet C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L34-L39

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

theorem Formalism.L2.FormalSeriesBounds.jet_C (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a) G = a * constantCoeff G := by sorry
