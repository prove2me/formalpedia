-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_lseries_at_two
-- name    : Formalism.ZeroFreeDirichlet.one_le_lseries_at_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:43:36.231298+00:00
-- url     : https://prove2.me/theorems/8a4adaa1-2294-4118-a889-f63e264bacf8
-- title:
--   Zero Free Dirichlet: one le lseries at two
-- statement:
--   The Zero Free Dirichlet construction uses the one le lseries at two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean#L10-L20

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

theorem Formalism.ZeroFreeDirichlet.one_le_lseries_at_two {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) : 1 ≤ LSeries a 2 := by sorry
