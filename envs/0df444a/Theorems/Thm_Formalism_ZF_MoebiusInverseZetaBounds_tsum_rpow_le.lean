-- Prove2me | Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_tsum_rpow_le
-- name    : Formalism.ZF.MoebiusInverseZetaBounds.tsum_rpow_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:36.007523+00:00
-- url     : https://prove2.me/theorems/5a746679-d0f1-48e5-aa98-b324957c5e10
-- title:
--   Moebius Inverse Zeta Bounds: tsum rpow le
-- statement:
--   The Moebius Inverse Zeta Bounds construction uses the tsum rpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L43-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L43-L67

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

theorem Formalism.ZF.MoebiusInverseZetaBounds.tsum_rpow_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by sorry
