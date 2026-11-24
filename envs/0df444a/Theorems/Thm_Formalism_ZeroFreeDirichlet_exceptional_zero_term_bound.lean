-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exceptional_zero_term_bound
-- name    : Formalism.ZeroFreeDirichlet.exceptional_zero_term_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:43:19.979805+00:00
-- url     : https://prove2.me/theorems/25528f87-ea53-4f98-a6e6-bf511277c888
-- title:
--   Zero Free Dirichlet: exceptional zero term bound
-- statement:
--   The Zero Free Dirichlet construction uses the exceptional zero term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L107-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L107-L153

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

theorem Formalism.ZeroFreeDirichlet.exceptional_zero_term_bound (x A q cE β : ℝ) (hx : 2 ≤ x) (hA : 0 < A) (hq : 1 ≤ q)
    (hqL : q ≤ Real.log x ^ A) (hcE : 0 < cE) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β ≤ 1 - cE * q ^ (-(1 / (2 * A)))) :
    ‖(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) := by sorry
