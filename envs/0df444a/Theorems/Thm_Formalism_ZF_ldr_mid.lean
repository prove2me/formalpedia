-- Prove2me | Theorems.Thm_Formalism_ZF_ldr_mid
-- name    : Formalism.ZF.ldr_mid
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:45.582264+00:00
-- url     : https://prove2.me/theorems/5634bc8d-dce8-4efe-932f-625d42e8ff01
-- title:
--   ZF: ldr mid
-- statement:
--   The ZF construction uses the ldr mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LdrMid.lean#L9-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LdrMid.lean#L9-L124

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LdrInvSubOneLe
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LdrMid
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

theorem Formalism.ZF.ldr_mid {c₀ : ℝ}
    (hZ0 : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hc₀ : 0 < c₀) (hG : ZetaGrowth) (hI : ZetaInvBound) (hLL : LandauLocal) {σ t : ℝ}
    (hL : 24 ≤ Real.log (|t| + 2))
    (hσlo : 1 - (c₀ / 4) / Real.log (|t| + 2) ≤ σ) (hσlo' : 1 - 1 / Real.log (|t| + 2) ≤ σ)
    (hσhi : σ ≤ 1 + 1 / Real.log (|t| + 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)
        + 1 / (((σ : ℂ) + t * I) - 1)‖
      ≤ (1441 + 60 / c₀) * Real.log (|t| + 2) ^ 2 := by sorry
