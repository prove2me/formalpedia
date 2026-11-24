-- Prove2me | Theorems.Thm_Formalism_ZF_perron_continuous_Fy
-- name    : Formalism.ZF.perron_continuous_Fy
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:41:49.719801+00:00
-- url     : https://prove2.me/theorems/d99bb1ce-7b9e-4a6b-a6e3-e42742b39d66
-- title:
--   ZF: perron continuous Fy
-- statement:
--   The ZF construction uses the perron continuous Fy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L151-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L151-L178

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.perron_continuous_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by sorry
