-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_le_of_log_bound
-- name    : Formalism.ZeroFreeDirichlet.norm_le_of_log_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:37.801716+00:00
-- url     : https://prove2.me/theorems/049c40ab-346e-46c1-a28f-affefd6d2e03
-- title:
--   Zero Free Dirichlet: norm le of log bound
-- statement:
--   The Zero Free Dirichlet construction uses the norm le of log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean#L10-L18

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqKeyOf
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

theorem Formalism.ZeroFreeDirichlet.norm_le_of_log_bound {z : ℂ} {CL : ℝ} (q : ℕ) [NeZero q] (h : ‖z‖ ≤ CL * Real.log (3 * q)) :
    ‖z‖ ≤ |CL| * (3 * q) := by sorry
