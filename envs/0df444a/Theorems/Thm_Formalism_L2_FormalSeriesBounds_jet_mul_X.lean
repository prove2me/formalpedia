-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_mul_X
-- name    : Formalism.L2.FormalSeriesBounds.jet_mul_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:59:24.263125+00:00
-- url     : https://prove2.me/theorems/b8f343f5-657e-5f0c-a0d7-332467ccf1b9
-- title:
--   Formal Series Bounds: jet mul X
-- statement:
--   The Formal Series Bounds construction uses the jet mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L64-L74

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.L2.FormalSeriesBounds.jet_mul_X (p : MvPolynomial σ C) (x : σ) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.X x) G = jetAt0 p (dVar x G) := by sorry
