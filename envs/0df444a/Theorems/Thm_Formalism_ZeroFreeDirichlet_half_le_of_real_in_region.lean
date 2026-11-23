-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_half_le_of_real_in_region
-- name    : Formalism.ZeroFreeDirichlet.half_le_of_real_in_region
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:01.236815+00:00
-- url     : https://prove2.me/theorems/13fd34f3-f1a9-4c5f-8eb6-6e33b2798747
-- title:
--   Zero Free Dirichlet: half le of real in region
-- statement:
--   The Zero Free Dirichlet construction uses the half le of real in region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean#L27-L43

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

theorem Formalism.ZeroFreeDirichlet.half_le_of_real_in_region {c₁ : ℝ} (h : c₁ ≤ 1 / 20) {q : ℕ} [NeZero q] {β : ℝ} (hs : InRegion c₁ q (β : ℂ)) :
    1 / 2 ≤ β := by sorry
