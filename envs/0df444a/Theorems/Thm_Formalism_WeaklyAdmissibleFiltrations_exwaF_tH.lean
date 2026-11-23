-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_tH
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaF_tH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:43.535883+00:00
-- url     : https://prove2.me/theorems/53bea864-a481-4982-8fb5-6acb368e49c7
-- title:
--   Weakly Admissible Filtrations: exwa F t H
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa F t H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L77-L88

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwaF_tH (c : LL) (hc : c ≠ 0) (D' : Submodule LL (ZMod n → LL)) :
    (exwaF c hc).tH D' =
      -∑ τ : ZMod n, (finrank LL ↥((LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL)) ⊓ D') : ℤ) := by sorry
