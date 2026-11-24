-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_tH_top
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaF_tH_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:33.125594+00:00
-- url     : https://prove2.me/theorems/1d3d61bb-3f36-47cc-b1f3-bc54395f950f
-- title:
--   Weakly Admissible Filtrations: exwa F t H top
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa F t H top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L90-L96

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
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
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]

theorem Formalism.WeaklyAdmissibleFiltrations.exwaF_tH_top (c : LL) (hc : c ≠ 0) : (exwaF (n := n) c hc).tH ⊤ = -(n : ℤ) := by sorry
