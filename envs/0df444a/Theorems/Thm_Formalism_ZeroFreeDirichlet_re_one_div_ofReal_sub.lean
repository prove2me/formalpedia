-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_re_one_div_ofReal_sub
-- name    : Formalism.ZeroFreeDirichlet.re_one_div_ofReal_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:43:48.727421+00:00
-- url     : https://prove2.me/theorems/f56b771d-3be9-412a-aaa9-7b177a0231fc
-- title:
--   Zero Free Dirichlet: re one div of Real sub
-- statement:
--   The Zero Free Dirichlet construction uses the re one div of Real sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealSmallTOf.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealSmallTOf.lean#L22-L26

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealSmallTOf
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

theorem Formalism.ZeroFreeDirichlet.re_one_div_ofReal_sub (σ : ℝ) (ρ : ℂ) :
    (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by sorry
