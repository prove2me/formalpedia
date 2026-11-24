-- Prove2me | Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_rpow_le_integral
-- name    : Formalism.ZF.MoebiusInverseZetaBounds.rpow_le_integral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:49.480811+00:00
-- url     : https://prove2.me/theorems/61c31030-6591-4761-a957-259ee4a0fd65
-- title:
--   Moebius Inverse Zeta Bounds: rpow le integral
-- statement:
--   The Moebius Inverse Zeta Bounds construction uses the rpow le integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L15-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L15-L41

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology LSeries ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.MoebiusInverseZetaBounds

theorem Formalism.ZF.MoebiusInverseZetaBounds.rpow_le_integral {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    (x + 1) ^ (-σ - 1) ≤ (x ^ (-σ) - (x + 1) ^ (-σ)) / σ := by sorry
