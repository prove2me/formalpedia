-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_mul_C
-- name    : Formalism.L2.FormalSeriesBounds.jet_mul_C
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:59:20.492805+00:00
-- url     : https://prove2.me/theorems/b746952b-6f89-53bc-90c8-6259a3845f65
-- title:
--   Formal Series Bounds: jet mul C
-- statement:
--   The Formal Series Bounds construction uses the jet mul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L76-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMJet.lean#L76-L91

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

theorem Formalism.L2.FormalSeriesBounds.jet_mul_C (p : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.C a) G = a * jetAt0 p G := by sorry
