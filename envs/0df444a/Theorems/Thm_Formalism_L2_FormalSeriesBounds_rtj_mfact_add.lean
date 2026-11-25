-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_mfact_add
-- name    : Formalism.L2.FormalSeriesBounds.rtj_mfact_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:55.574803+00:00
-- url     : https://prove2.me/theorems/aacf0704-04f5-4ad6-b711-15e9f9ebe855
-- title:
--   Formal Series Bounds: rtj mfact add
-- statement:
--   The Formal Series Bounds construction uses the rtj mfact add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L72-L75

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
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_mfact_add {a b : σ →₀ ℕ} (h : Disjoint a.support b.support) :
    mfact (a + b) = mfact a * mfact b := by sorry
