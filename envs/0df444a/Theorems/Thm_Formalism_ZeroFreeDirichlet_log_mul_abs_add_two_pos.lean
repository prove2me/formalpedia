-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_log_mul_abs_add_two_pos
-- name    : Formalism.ZeroFreeDirichlet.log_mul_abs_add_two_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:53.950943+00:00
-- url     : https://prove2.me/theorems/d31fe4fa-9da6-4813-acda-7a160f1e52cf
-- title:
--   Zero Free Dirichlet: log mul abs add two pos
-- statement:
--   The Zero Free Dirichlet construction uses the log mul abs add two pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L18-L19

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

theorem Formalism.ZeroFreeDirichlet.log_mul_abs_add_two_pos (q : ℕ) [NeZero q] (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := by sorry
