-- Prove2me | Theorems.Thm_Formalism_ZF_zfo_zero_re_lt
-- name    : Formalism.ZF.zfo_zero_re_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:26.888222+00:00
-- url     : https://prove2.me/theorems/d5c00b5a-41ec-4596-9a6d-7288237df5b9
-- title:
--   ZF: zfo zero re lt
-- statement:
--   The ZF construction uses the zfo zero re lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoTermReNonneg.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZfoTermReNonneg.lean#L9-L12

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

theorem Formalism.ZF.zfo_zero_re_lt {ρ : ℂ} {σ : ℝ} (hσ : 1 < σ) (h : riemannZeta ρ = 0) : ρ.re < σ := by sorry
