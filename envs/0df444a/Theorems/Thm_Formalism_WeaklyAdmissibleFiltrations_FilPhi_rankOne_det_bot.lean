-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_rankOne_det_bot
-- name    : Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_det_bot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:55.640705+00:00
-- url     : https://prove2.me/theorems/b4b90e3b-c5b1-41df-bf78-f2989bffdb6c
-- title:
--   Fil Phi: rank One det bot
-- statement:
--   The Fil Phi construction uses the rank One det bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/RankOne.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/RankOne.lean#L56-L58

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

theorem Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_det_bot (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊥ : Submodule LL D), F.φ x ∈ (⊥ : Submodule LL D)) :
    LinearMap.det (F.φres ⊥ h) = 1 := by sorry
