-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_rankOne_isSub_bot_or_top
-- name    : Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_isSub_bot_or_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:53.794595+00:00
-- url     : https://prove2.me/theorems/f62eab61-bde7-48f9-99c1-2d0bfd9dbbe9
-- title:
--   Fil Phi: rank One is Sub bot or top
-- statement:
--   The Fil Phi construction uses the rank One is Sub bot or top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/RankOne.lean#L14-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/RankOne.lean#L14-L49

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
open Formalism.WeaklyAdmissibleFiltrations.FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

theorem Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_isSub_bot_or_top [NeZero n] (F : FilPhi LL D n Emb)
    (hl : ∀ i, finrank LL ↥(F.Dl i) = 1) (D' : Submodule LL D) (hD : F.IsSub D') :
    D' = ⊥ ∨ D' = ⊤ := by sorry
