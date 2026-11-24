-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_bounded_of_exp_sqrt_lt_pow
-- name    : Formalism.ZeroFreeDirichlet.bounded_of_exp_sqrt_lt_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:33.381301+00:00
-- url     : https://prove2.me/theorems/7e8cecbe-58a5-4937-9372-fa53a94d7910
-- title:
--   Zero Free Dirichlet: bounded of exp sqrt lt pow
-- statement:
--   The Zero Free Dirichlet construction uses the bounded of exp sqrt lt pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L155-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L155-L170

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.bounded_of_exp_sqrt_lt_pow (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ L : ℝ, 0 < L → Real.exp (c * Real.sqrt L) < L ^ A → L ≤ U := by sorry
