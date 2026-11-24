-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_iteratedDeriv_lseries_alternating_nonneg
-- name    : Formalism.ZeroFreeDirichlet.iteratedDeriv_lseries_alternating_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:43:24.217973+00:00
-- url     : https://prove2.me/theorems/24435b6f-2b45-4890-a220-c20dbd5b9927
-- title:
--   Zero Free Dirichlet: iterated Deriv lseries alternating nonneg
-- statement:
--   The Zero Free Dirichlet construction uses the iterated Deriv lseries alternating nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean#L22-L28

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivInvSubOneAtTwo
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.iteratedDeriv_lseries_alternating_nonneg {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (LSeries a) 2 := by sorry
