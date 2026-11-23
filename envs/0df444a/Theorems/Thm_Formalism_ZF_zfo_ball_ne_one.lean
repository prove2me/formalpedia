-- Prove2me | Theorems.Thm_Formalism_ZF_zfo_ball_ne_one
-- name    : Formalism.ZF.zfo_ball_ne_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:29.22169+00:00
-- url     : https://prove2.me/theorems/bdf99af8-7838-4954-8b00-13431eaad3e6
-- title:
--   ZF: zfo ball ne one
-- statement:
--   The ZF construction uses the zfo ball ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoGrowthBall.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoGrowthBall.lean#L27-L35

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.zfo_ball_ne_one {σ τ : ℝ} (hτ : 3 ≤ |τ|) {w : ℂ}
    (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) : w ≠ 1 ∧ 5 / 2 ≤ |w.im| := by sorry
