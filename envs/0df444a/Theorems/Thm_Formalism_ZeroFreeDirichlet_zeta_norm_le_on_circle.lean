-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_zeta_norm_le_on_circle
-- name    : Formalism.ZeroFreeDirichlet.zeta_norm_le_on_circle
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:39.888556+00:00
-- url     : https://prove2.me/theorems/819a2ac3-13fa-4af4-896c-d29d5e4c52b1
-- title:
--   Zero Free Dirichlet: zeta norm le on circle
-- statement:
--   The Zero Free Dirichlet construction uses the zeta norm le on circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqGrowth.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqGrowth.lean#L29-L46

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

theorem Formalism.ZeroFreeDirichlet.zeta_norm_le_on_circle {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) : ‖riemannZeta s‖ ≤ 14 := by sorry
