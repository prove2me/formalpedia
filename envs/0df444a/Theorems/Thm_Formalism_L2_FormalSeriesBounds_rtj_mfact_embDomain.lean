-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_mfact_embDomain
-- name    : Formalism.L2.FormalSeriesBounds.rtj_mfact_embDomain
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:14.266966+00:00
-- url     : https://prove2.me/theorems/40257840-bcd6-495b-b0e4-86e277c7f715
-- title:
--   Formal Series Bounds: rtj mfact emb Domain
-- statement:
--   The Formal Series Bounds construction uses the rtj mfact emb Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L211-L213

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

theorem Formalism.L2.FormalSeriesBounds.rtj_mfact_embDomain (e : σ ↪ τ) (m : σ →₀ ℕ) : mfact (Finsupp.embDomain e m) = mfact m := by sorry
