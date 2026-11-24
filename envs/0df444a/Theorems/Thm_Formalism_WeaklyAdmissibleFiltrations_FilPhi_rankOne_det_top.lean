-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_rankOne_det_top
-- name    : Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_det_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:38:05.371978+00:00
-- url     : https://prove2.me/theorems/0eaf4d78-e57f-4c39-80a8-b2a373cc2537
-- title:
--   Fil Phi: rank One det top
-- statement:
--   The Fil Phi construction uses the rank One det top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/RankOne.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/RankOne.lean#L60-L65

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

theorem Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_det_top (F : FilPhi LL D n Emb) (h : ∀ x ∈ (⊤ : Submodule LL D), F.φ x ∈ (⊤ : Submodule LL D)) :
    LinearMap.det (F.φres ⊤ h) = LinearMap.det (F.φ : D →ₗ[LL] D) := by sorry
