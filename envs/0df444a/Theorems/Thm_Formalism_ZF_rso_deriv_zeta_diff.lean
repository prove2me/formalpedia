-- Prove2me | Theorems.Thm_Formalism_ZF_rso_deriv_zeta_diff
-- name    : Formalism.ZF.rso_deriv_zeta_diff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:30.626587+00:00
-- url     : https://prove2.me/theorems/335f54e9-98eb-4cf9-a417-7a0c750c4eab
-- title:
--   ZF: rso deriv zeta diff
-- statement:
--   The ZF construction uses the rso deriv zeta diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectShiftOf.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectShiftOf.lean#L15-L18

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

theorem Formalism.ZF.rso_deriv_zeta_diff : DifferentiableOn ℂ (deriv riemannZeta) {w : ℂ | w ≠ 1} := by sorry
