-- Prove2me | Theorems.Thm_Formalism_ZF_perron_norm_LSeries_le
-- name    : Formalism.ZF.perron_norm_LSeries_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:40:57.027707+00:00
-- url     : https://prove2.me/theorems/767892cb-1447-472d-9dab-e99f7f7d168d
-- title:
--   ZF: perron norm LSeries le
-- statement:
--   The ZF construction uses the perron norm LSeries le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L107-L117

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

theorem Formalism.ZF.perron_norm_LSeries_le {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖LSeries ↗Λ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by sorry
