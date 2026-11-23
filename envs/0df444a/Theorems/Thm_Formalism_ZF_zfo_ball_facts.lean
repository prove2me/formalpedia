-- Prove2me | Theorems.Thm_Formalism_ZF_zfo_ball_facts
-- name    : Formalism.ZF.zfo_ball_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:20.945824+00:00
-- url     : https://prove2.me/theorems/16723077-d7d6-40ac-b7ae-a930ed7f09e9
-- title:
--   ZF: zfo ball facts
-- statement:
--   The ZF construction uses the zfo ball facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoGrowthBall.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoGrowthBall.lean#L9-L25

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

theorem Formalism.ZF.zfo_ball_facts {σ τ : ℝ} {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    |w.re - σ| ≤ 1 / 2 ∧ |w.im - τ| ≤ 1 / 2 ∧ ‖w‖ ≤ |σ| + |τ| + 1 / 2 := by sorry
