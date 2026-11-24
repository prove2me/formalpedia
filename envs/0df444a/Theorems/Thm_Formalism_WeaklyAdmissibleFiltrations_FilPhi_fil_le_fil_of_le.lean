-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_fil_le_fil_of_le
-- name    : Formalism.WeaklyAdmissibleFiltrations.FilPhi.fil_le_fil_of_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:38:08.336802+00:00
-- url     : https://prove2.me/theorems/38c2c707-65a6-42ae-8784-2ba9174dd36f
-- title:
--   Fil Phi: fil le fil of le
-- statement:
--   The Fil Phi construction uses the fil le fil of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/JumpsPFilAntitoneOfLe.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/JumpsPFilAntitoneOfLe.lean#L12-L16

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe
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
open Formalism.WeaklyAdmissibleFiltrations.FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

theorem Formalism.WeaklyAdmissibleFiltrations.FilPhi.fil_le_fil_of_le (F : FilPhi LL D n Emb) (τ : Emb) {b a : ℤ} (hba : b ≤ a) :
    F.Fil τ a ≤ F.Fil τ b := by sorry
