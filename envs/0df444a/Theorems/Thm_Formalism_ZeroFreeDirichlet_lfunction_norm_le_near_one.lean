-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_lfunction_norm_le_near_one
-- name    : Formalism.ZeroFreeDirichlet.lfunction_norm_le_near_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:59.18594+00:00
-- url     : https://prove2.me/theorems/138360e7-2af7-4f97-8260-7186c2142d20
-- title:
--   Zero Free Dirichlet: lfunction norm le near one
-- statement:
--   The Zero Free Dirichlet construction uses the lfunction norm le near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L89-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L89-L126

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.lfunction_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) (hw4 : 1 / 4 ≤ w.re) (hw2 : ‖w‖ ≤ 2) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by sorry
