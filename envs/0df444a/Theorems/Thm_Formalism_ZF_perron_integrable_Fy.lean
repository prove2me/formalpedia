-- Prove2me | Theorems.Thm_Formalism_ZF_perron_integrable_Fy
-- name    : Formalism.ZF.perron_integrable_Fy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:35.58392+00:00
-- url     : https://prove2.me/theorems/263d1f83-5f8b-4d44-94dc-966e1bc28e1a
-- title:
--   ZF: perron integrable Fy
-- statement:
--   The ZF construction uses the perron integrable Fy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L180-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L180-L199

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

theorem Formalism.ZF.perron_integrable_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by sorry
