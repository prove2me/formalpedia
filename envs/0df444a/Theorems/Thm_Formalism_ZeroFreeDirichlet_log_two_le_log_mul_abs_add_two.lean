-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_log_two_le_log_mul_abs_add_two
-- name    : Formalism.ZeroFreeDirichlet.log_two_le_log_mul_abs_add_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:07.552408+00:00
-- url     : https://prove2.me/theorems/4b031260-319a-4029-ad39-8824c60d7106
-- title:
--   Zero Free Dirichlet: log two le log mul abs add two
-- statement:
--   The Zero Free Dirichlet construction uses the log two le log mul abs add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L12-L16

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
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

theorem Formalism.ZeroFreeDirichlet.log_two_le_log_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by sorry
