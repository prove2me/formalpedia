-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_degree_embDomain
-- name    : Formalism.L2.FormalSeriesBounds.rtj_degree_embDomain
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:34.879871+00:00
-- url     : https://prove2.me/theorems/e11c0f10-8e66-49bb-a100-dfce760ae5e0
-- title:
--   Formal Series Bounds: rtj degree emb Domain
-- statement:
--   The Formal Series Bounds construction uses the rtj degree emb Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L278-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L278-L280

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

theorem Formalism.L2.FormalSeriesBounds.rtj_degree_embDomain (e : σ ↪ τ) (μ : σ →₀ ℕ) : (Finsupp.embDomain e μ).degree = μ.degree := by sorry
