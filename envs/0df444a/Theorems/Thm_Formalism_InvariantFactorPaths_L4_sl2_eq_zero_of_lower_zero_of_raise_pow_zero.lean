-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_eq_zero_of_lower_zero_of_raise_pow_zero
-- name    : Formalism.InvariantFactorPaths.L4.sl2_eq_zero_of_lower_zero_of_raise_pow_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:46.588129+00:00
-- url     : https://prove2.me/theorems/b553a897-811b-4f3e-868d-7f12890957a6
-- title:
--   L4: sl2 eq zero of lower zero of raise pow zero
-- statement:
--   The L4 construction uses the sl2 eq zero of lower zero of raise pow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Sl2RaisePowSuccLowerApplyEq.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Sl2RaisePowSuccLowerApplyEq.lean#L41-L59

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

theorem Formalism.InvariantFactorPaths.L4.sl2_eq_zero_of_lower_zero_of_raise_pow_zero (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) (hef : ∀ x, e (f x) - f (e x) = h x)
    {u : V} {μ : ℤ} (hu : h u = ((μ : ℤ) : k) • u) (hf : f u = 0) :
    ∀ j : ℕ, μ + j ≤ 0 → (e ^ j) u = 0 → u = 0 := by sorry
