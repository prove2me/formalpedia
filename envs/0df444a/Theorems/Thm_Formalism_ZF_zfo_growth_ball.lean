-- Prove2me | Theorems.Thm_Formalism_ZF_zfo_growth_ball
-- name    : Formalism.ZF.zfo_growth_ball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:45.919781+00:00
-- url     : https://prove2.me/theorems/3428a9e1-f7a4-48da-897a-5f72c003637d
-- title:
--   ZF: zfo growth ball
-- statement:
--   The ZF construction uses the zfo growth ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoGrowthBall.lean#L42-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoGrowthBall.lean#L42-L70

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

theorem Formalism.ZF.zfo_growth_ball (hG : ZetaGrowth) {σ τ T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hτ : 3 ≤ |τ|)
    (hτT : |τ| ≤ 2 * T) {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    ‖riemannZeta w‖ ≤ 6 * (T + 2) := by sorry
