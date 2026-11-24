-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_two
-- name    : Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:59.936708+00:00
-- url     : https://prove2.me/theorems/f3364d35-4c95-4b33-836c-4a3076153458
-- title:
--   Neg: rep two
-- statement:
--   The Neg construction uses the rep two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L73-L87

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

theorem Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_two (c : ℕ) (hc : c % 8 = 3) : ∃ x y : ℤ_[2], x ^ 2 + (c : ℤ_[2]) * y ^ 2 = -1 := by sorry
