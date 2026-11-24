-- Prove2me | Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_norm_term_moebius_le
-- name    : Formalism.ZF.MoebiusInverseZetaBounds.norm_term_moebius_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:48.888736+00:00
-- url     : https://prove2.me/theorems/f4cf8278-7674-4d51-972a-2e2864252d81
-- title:
--   Moebius Inverse Zeta Bounds: norm term moebius le
-- statement:
--   The Moebius Inverse Zeta Bounds construction uses the norm term moebius le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L76-L81

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

theorem Formalism.ZF.MoebiusInverseZetaBounds.norm_term_moebius_le (s : ℂ) (n : ℕ) :
    ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by sorry
