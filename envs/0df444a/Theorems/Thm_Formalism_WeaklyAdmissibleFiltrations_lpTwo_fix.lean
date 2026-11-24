-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_lpTwo_fix
-- name    : Formalism.WeaklyAdmissibleFiltrations.lpTwo_fix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:14.995838+00:00
-- url     : https://prove2.me/theorems/10d78be5-5c42-4c8b-ac49-b30e2b10cd52
-- title:
--   Weakly Admissible Filtrations: lp Two fix
-- statement:
--   The Weakly Admissible Filtrations construction uses the lp Two fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExistsPeriodRingDataHolds.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExistsPeriodRingDataHolds.lean#L71-L84

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExistsPeriodRingDataHolds
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
open LaurentPolynomial

theorem Formalism.WeaklyAdmissibleFiltrations.lpTwo_fix (f : LaurentPolynomial ℚ) (h : lpScaleE lpTwo f = f) :
    algebraMap ℚ (LaurentPolynomial ℚ) (f.coeff 0) = f := by sorry
