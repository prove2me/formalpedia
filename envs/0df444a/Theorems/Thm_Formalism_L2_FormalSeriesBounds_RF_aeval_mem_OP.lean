-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_aeval_mem_OP
-- name    : Formalism.L2.FormalSeriesBounds.RF.aeval_mem_OP
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:53:07.218287+00:00
-- url     : https://prove2.me/theorems/89392268-4a9c-4fb5-aead-0d44140e6bb4
-- title:
--   RF: aeval mem OP
-- statement:
--   The RF construction uses the aeval mem OP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemC.lean#L125-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemC.lean#L125-L138

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksCChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.RF.aeval_mem_OP {C : Type} [Field C] {O : Subring C} {σ τ : Type} (f : σ → MvPolynomial τ C)
    (hf : ∀ x, f x ∈ OP O τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) : MvPolynomial.aeval f P ∈ OP O τ := by sorry
