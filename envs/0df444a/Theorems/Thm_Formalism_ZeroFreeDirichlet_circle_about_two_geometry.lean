-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_circle_about_two_geometry
-- name    : Formalism.ZeroFreeDirichlet.circle_about_two_geometry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:55.090469+00:00
-- url     : https://prove2.me/theorems/f3379320-2603-4bf8-96e5-a61ed052d6e2
-- title:
--   Zero Free Dirichlet: circle about two geometry
-- statement:
--   The Zero Free Dirichlet construction uses the circle about two geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqGrowth.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqGrowth.lean#L11-L27

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqGrowth
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

theorem Formalism.ZeroFreeDirichlet.circle_about_two_geometry {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) :
    1 / 2 ≤ s.re ∧ ‖s‖ ≤ 7 / 2 ∧ 1 / 2 ≤ ‖s - 1‖ := by sorry
