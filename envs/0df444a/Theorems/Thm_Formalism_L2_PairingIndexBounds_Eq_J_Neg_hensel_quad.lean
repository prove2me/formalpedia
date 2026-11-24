-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_hensel_quad
-- name    : Formalism.L2.PairingIndexBounds.Eq.J.Neg.hensel_quad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:10.458387+00:00
-- url     : https://prove2.me/theorems/0eaded6d-c5e4-40bb-93fe-1d3550fc74d9
-- title:
--   Neg: hensel quad
-- statement:
--   The Neg construction uses the hensel quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L7-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq.J.Neg

theorem Formalism.L2.PairingIndexBounds.Eq.J.Neg.hensel_quad (p : ℕ) [Fact p.Prime] (a b t : ℤ)
    (h : ‖((a * t ^ 2 + b : ℤ) : ℤ_[p])‖ < ‖((2 * a * t : ℤ) : ℤ_[p])‖ ^ 2) :
    ∃ z : ℤ_[p], (a : ℤ_[p]) * z ^ 2 + (b : ℤ_[p]) = 0 := by sorry
