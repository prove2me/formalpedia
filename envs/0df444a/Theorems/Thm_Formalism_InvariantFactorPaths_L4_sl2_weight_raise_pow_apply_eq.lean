-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_weight_raise_pow_apply_eq
-- name    : Formalism.InvariantFactorPaths.L4.sl2_weight_raise_pow_apply_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:50.956698+00:00
-- url     : https://prove2.me/theorems/984c3764-084c-470e-99bc-84e7621945b4
-- title:
--   L4: sl2 weight raise pow apply eq
-- statement:
--   The L4 construction uses the sl2 weight raise pow apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Sl2RaisePowSuccLowerApplyEq.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Sl2RaisePowSuccLowerApplyEq.lean#L8-L19

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
variable {k V : Type} [Field k] [CharZero k] [AddCommGroup V] [Module k V] {e f h : V →ₗ[k] V}

theorem Formalism.InvariantFactorPaths.L4.sl2_weight_raise_pow_apply_eq (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) {u : V} {μ : k} (hu : h u = μ • u) (m : ℕ) :
    h ((e ^ m) u) = (μ + 2 * (m : k)) • (e ^ m) u := by sorry
