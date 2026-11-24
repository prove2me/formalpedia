-- Prove2me | Theorems.Thm_Formalism_ZF_norm_logDeriv_le_lamF
-- name    : Formalism.ZF.norm_logDeriv_le_lamF
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:48.101834+00:00
-- url     : https://prove2.me/theorems/d4745369-9283-42d3-8b0a-598ca9c4f409
-- title:
--   ZF: norm log Deriv le lam F
-- statement:
--   The ZF construction uses the norm log Deriv le lam F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L12-L22

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.norm_logDeriv_le_lamF {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ lamF s.re := by sorry
