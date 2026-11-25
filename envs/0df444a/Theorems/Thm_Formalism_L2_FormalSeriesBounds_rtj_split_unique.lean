-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_split_unique
-- name    : Formalism.L2.FormalSeriesBounds.rtj_split_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:12.703265+00:00
-- url     : https://prove2.me/theorems/51d77a85-de64-433f-9027-af9e0ba3860c
-- title:
--   Formal Series Bounds: rtj split unique
-- statement:
--   The Formal Series Bounds construction uses the rtj split unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L27-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L27-L50

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

theorem Formalism.L2.FormalSeriesBounds.rtj_split_unique {A : Set σ} {a b c d : σ →₀ ℕ} (ha : (↑a.support : Set σ) ⊆ A)
    (hb : (↑b.support : Set σ) ⊆ Aᶜ) (hc : (↑c.support : Set σ) ⊆ A)
    (hd : (↑d.support : Set σ) ⊆ Aᶜ) (h : c + d = a + b) : c = a ∧ d = b := by sorry
