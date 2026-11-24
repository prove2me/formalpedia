-- Prove2me | Theorems.Thm_Formalism_ZF_zfo_term_re_nonneg
-- name    : Formalism.ZF.zfo_term_re_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:23.321001+00:00
-- url     : https://prove2.me/theorems/75124680-7015-410a-a923-94a2f5a46e33
-- title:
--   ZF: zfo term re nonneg
-- statement:
--   The ZF construction uses the zfo term re nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoTermReNonneg.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoTermReNonneg.lean#L14-L18

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoTermReNonneg
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

theorem Formalism.ZF.zfo_term_re_nonneg {z ρ : ℂ} (n : ℕ) (h : ρ.re < z.re) :
    0 ≤ ((n : ℂ) / (z - ρ)).re := by sorry
