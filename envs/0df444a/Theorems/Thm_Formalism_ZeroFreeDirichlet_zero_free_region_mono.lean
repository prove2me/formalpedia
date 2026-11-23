-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_zero_free_region_mono
-- name    : Formalism.ZeroFreeDirichlet.zero_free_region_mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:32.850116+00:00
-- url     : https://prove2.me/theorems/84d879dc-a7e7-4858-b736-641301bdde4f
-- title:
--   Zero Free Dirichlet: zero free region mono
-- statement:
--   The Zero Free Dirichlet construction uses the zero free region mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L17-L25

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.zero_free_region_mono {c c' : ℝ} (h : c ≤ c') {q : ℕ} [NeZero q] {s : ℂ} (hs : InRegion c q s) :
    InRegion c' q s := by sorry
