-- Prove2me | Theorems.Thm_Formalism_ZF_zfo_large
-- name    : Formalism.ZF.zfo_large
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:16.052882+00:00
-- url     : https://prove2.me/theorems/f8106a40-3b11-4d60-939d-be270d661308
-- title:
--   ZF: zfo large
-- statement:
--   The ZF construction uses the zfo large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoNegReLeNorm.lean#L14-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoNegReLeNorm.lean#L14-L93

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoTermReNonneg
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoNegReLeNorm
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

theorem Formalism.ZF.zfo_large (h341 : ThreeFourOne) (hLDR : LogDerivRight) (hG : ZetaGrowth)
    (hI : ZetaInvBound) (hLL : LandauLocal) :
    ∃ t₀ : ℝ, 3 ≤ t₀ ∧ ∀ β t : ℝ, t₀ ≤ |t| → riemannZeta ((β : ℂ) + t * I) = 0 →
      β < 1 - (1 / 200000) / Real.log (|t| + 2) := by sorry
