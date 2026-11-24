-- Prove2me | Theorems.Thm_Formalism_ZF_rso_Fy_diff
-- name    : Formalism.ZF.rso_Fy_diff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:46.279776+00:00
-- url     : https://prove2.me/theorems/b2ae5237-e6d5-4379-8311-24d3691da670
-- title:
--   ZF: rso Fy diff
-- statement:
--   The ZF construction uses the rso Fy diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectShiftOf.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectShiftOf.lean#L20-L30

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf
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
open Formalism Formalism.ZF

theorem Formalism.ZF.rso_Fy_diff (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) : DifferentiableAt ℂ (Fy y) w := by sorry
