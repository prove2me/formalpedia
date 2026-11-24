-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_nsmul_top
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwa_nsmul_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:40:46.705832+00:00
-- url     : https://prove2.me/theorems/c7340c63-1b44-457f-b580-23b3b35c3a53
-- title:
--   Weakly Admissible Filtrations: exwa nsmul top
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa nsmul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L130-L132

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
variable {LL : Type} [Field LL]

theorem Formalism.WeaklyAdmissibleFiltrations.exwa_nsmul_top (k : ℕ) (hk : k ≠ 0) : k • (⊤ : WithTop ℚ) = ⊤ := by sorry
