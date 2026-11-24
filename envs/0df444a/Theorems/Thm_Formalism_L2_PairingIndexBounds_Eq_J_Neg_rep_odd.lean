-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_odd
-- name    : Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_odd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:54.925795+00:00
-- url     : https://prove2.me/theorems/c0851e6d-acce-45d7-b15f-52d29b3c57d2
-- title:
--   Neg: rep odd
-- statement:
--   The Neg construction uses the rep odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L31-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L31-L71

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

theorem Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) :
    ∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1 := by sorry
