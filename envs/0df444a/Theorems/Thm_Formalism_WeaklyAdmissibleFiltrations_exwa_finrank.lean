-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_finrank
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwa_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:23.111842+00:00
-- url     : https://prove2.me/theorems/aafe35d0-81b6-4b6e-b869-456f124ef7ef
-- title:
--   Weakly Admissible Filtrations: exwa finrank
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L170-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L170-L171

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwa_finrank : finrank LL (ZMod n → LL) = n := by sorry
