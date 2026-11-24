-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_two_le_mul_abs_add_two
-- name    : Formalism.ZeroFreeDirichlet.two_le_mul_abs_add_two
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:22.874348+00:00
-- url     : https://prove2.me/theorems/e375b864-f789-4831-a303-74782c3f256b
-- title:
--   Zero Free Dirichlet: two le mul abs add two
-- statement:
--   The Zero Free Dirichlet construction uses the two le mul abs add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealLargeTOf.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealLargeTOf.lean#L27-L29

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

theorem Formalism.ZeroFreeDirichlet.two_le_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) : 2 ≤ (q : ℝ) * (|t| + 2) := by sorry
