-- Prove2me | Theorems.Thm_Formalism_ZF_lamF_eq_norm
-- name    : Formalism.ZF.lamF_eq_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:10.602123+00:00
-- url     : https://prove2.me/theorems/8f394beb-02f7-44dc-aff8-f12910918230
-- title:
--   ZF: lam F eq norm
-- statement:
--   The ZF construction uses the lam F eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L33-L37

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

theorem Formalism.ZF.lamF_eq_norm {σ : ℝ} (hσ : 1 < σ) : lamF σ = ‖L ↗Λ (σ : ℂ)‖ := by sorry
