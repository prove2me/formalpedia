-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_window_mult_lo
-- name    : Formalism.WeaklyAdmissibleFiltrations.pht_window_mult_lo
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:16.06431+00:00
-- url     : https://prove2.me/theorems/d4ace212-cabf-42c0-84a5-4c8e7e1f353c
-- title:
--   Weakly Admissible Filtrations: pht window mult lo
-- statement:
--   The Weakly Admissible Filtrations construction uses the pht window mult lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/Window.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/Window.lean#L24-L28

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
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
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

theorem Formalism.WeaklyAdmissibleFiltrations.pht_window_mult_lo (F : FilPhi LL D n Emb) (D' : Submodule LL D) (τ : Emb) (a : ℤ)
    (ha : a < F.lo) : F.mult D' τ a = 0 := by sorry
