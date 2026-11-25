-- Prove2me | Theorems.Thm_Formalism_ZF_norm_Dz_le
-- name    : Formalism.ZF.norm_Dz_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:57.24801+00:00
-- url     : https://prove2.me/theorems/e5545707-a69b-4325-9670-fcab7f63b92d
-- title:
--   ZF: norm Dz le
-- statement:
--   The ZF construction uses the norm Dz le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaGrowth.lean#L11-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaGrowth.lean#L11-L76

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
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
open ComplexPowerDifferenceIntegral

theorem Formalism.ZF.norm_Dz_le {s : ℂ} (hs : 0 < s.re) :
    ‖Dz s‖ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by sorry
