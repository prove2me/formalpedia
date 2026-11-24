-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_zero_free_region_mono_half
-- name    : Formalism.ZeroFreeDirichlet.zero_free_region_mono_half
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:11.609801+00:00
-- url     : https://prove2.me/theorems/219f7b33-be62-46a7-baf5-b25772f8d005
-- title:
--   Zero Free Dirichlet: zero free region mono half
-- statement:
--   The Zero Free Dirichlet construction uses the zero free region mono half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogTwoLeLogAnalyticConductor.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogTwoLeLogAnalyticConductor.lean#L22-L30

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
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

theorem Formalism.ZeroFreeDirichlet.zero_free_region_mono_half {c₁ : ℝ} (hc : 0 < c₁) (q : ℕ) [NeZero q] (s : ℂ)
    (h : InRegion (c₁ / 2) q s) : InRegion c₁ q s := by sorry
