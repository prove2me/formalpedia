-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_zeta_sub_pole_differentiable
-- name    : Formalism.ZeroFreeDirichlet.zeta_sub_pole_differentiable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:33.0221+00:00
-- url     : https://prove2.me/theorems/e5eebd1b-2994-4c8a-96fa-8e321cf8d87f
-- title:
--   Zero Free Dirichlet: zeta sub pole differentiable
-- statement:
--   The Zero Free Dirichlet construction uses the zeta sub pole differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean#L12-L25

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.zeta_sub_pole_differentiable : Differentiable ℂ zetaSubPole := by sorry
