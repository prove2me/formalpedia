-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaFiltration_neg_one_eq_span_single
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaFiltration_neg_one_eq_span_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:49.44028+00:00
-- url     : https://prove2.me/theorems/120540fc-259a-4fa6-a435-1883ba094f02
-- title:
--   Weakly Admissible Filtrations: exwa Filtration neg one eq span single
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa Filtration neg one eq span single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L70-L72

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwaFiltration_neg_one_eq_span_single (c : LL) (hc : c ≠ 0) (τ : ZMod n) :
    (exwaF c hc).Fil τ (-1) = LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL) := by sorry
