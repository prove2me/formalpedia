-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_supported
-- name    : Formalism.L2.FormalSeriesBounds.rtj_rename_supported
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:52.066497+00:00
-- url     : https://prove2.me/theorems/d9cbb300-31ee-4080-aef1-0ddf37c98a21
-- title:
--   Formal Series Bounds: rtj rename supported
-- statement:
--   The Formal Series Bounds construction uses the rtj rename supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L271-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L271-L276

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ τ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_rename_supported (e : σ ↪ τ) (P : MvPolynomial σ K) :
    MvPolynomial.rename e P ∈ MvPolynomial.supported K (Set.range e) := by sorry
