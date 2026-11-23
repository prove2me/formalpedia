-- Prove2me | Theorems.Thm_Formalism_ZF_perron_denom_bound
-- name    : Formalism.ZF.perron_denom_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:19.533169+00:00
-- url     : https://prove2.me/theorems/5a79ea63-bd30-4bb0-b30c-4856063d81c4
-- title:
--   ZF: perron denom bound
-- statement:
--   The ZF construction uses the perron denom bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L119-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L119-L143

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

theorem Formalism.ZF.perron_denom_bound {σ₀ : ℝ} (hσ : 1 < σ₀) (t : ℝ) :
    min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) ≤ ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖ := by sorry
