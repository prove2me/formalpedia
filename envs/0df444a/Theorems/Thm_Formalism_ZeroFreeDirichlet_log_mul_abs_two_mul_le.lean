-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_log_mul_abs_two_mul_le
-- name    : Formalism.ZeroFreeDirichlet.log_mul_abs_two_mul_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:53.323141+00:00
-- url     : https://prove2.me/theorems/076737c3-ebf2-4c07-bc2c-e7c51ed360cc
-- title:
--   Zero Free Dirichlet: log mul abs two mul le
-- statement:
--   The Zero Free Dirichlet construction uses the log mul abs two mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealLargeTOf.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealLargeTOf.lean#L31-L45

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealLargeTOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.log_mul_abs_two_mul_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by sorry
