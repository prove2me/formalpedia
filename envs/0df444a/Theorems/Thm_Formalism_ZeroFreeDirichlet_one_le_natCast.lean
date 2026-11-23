-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_natCast
-- name    : Formalism.ZeroFreeDirichlet.one_le_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:22.73838+00:00
-- url     : https://prove2.me/theorems/aa4bbed8-55be-4024-95fd-dbee3ab0103e
-- title:
--   Zero Free Dirichlet: one le nat Cast
-- statement:
--   The Zero Free Dirichlet construction uses the one le nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L9-L10

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

theorem Formalism.ZeroFreeDirichlet.one_le_natCast (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by sorry
