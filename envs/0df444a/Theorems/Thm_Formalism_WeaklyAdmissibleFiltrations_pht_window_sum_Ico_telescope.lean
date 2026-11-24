-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_window_sum_Ico_telescope
-- name    : Formalism.WeaklyAdmissibleFiltrations.pht_window_sum_Ico_telescope
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:39:55.339468+00:00
-- url     : https://prove2.me/theorems/f13c338f-3c87-40bb-893a-c77fa9627df1
-- title:
--   Weakly Admissible Filtrations: pht window sum Ico telescope
-- statement:
--   The Weakly Admissible Filtrations construction uses the pht window sum Ico telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/Window.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/Window.lean#L9-L19

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

theorem Formalism.WeaklyAdmissibleFiltrations.pht_window_sum_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by sorry
