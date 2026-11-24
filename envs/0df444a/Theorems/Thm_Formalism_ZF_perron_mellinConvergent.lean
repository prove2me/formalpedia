-- Prove2me | Theorems.Thm_Formalism_ZF_perron_mellinConvergent
-- name    : Formalism.ZF.perron_mellinConvergent
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:40:48.124963+00:00
-- url     : https://prove2.me/theorems/2a29908b-fa46-4f3c-898e-dab07346953c
-- title:
--   ZF: perron mellin Convergent
-- statement:
--   The ZF construction uses the perron mellin Convergent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L226-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L226-L245

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

theorem Formalism.ZF.perron_mellinConvergent {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => (Formalism.Sz x : ℂ)) ((-σ₀ : ℝ) : ℂ) := by sorry
