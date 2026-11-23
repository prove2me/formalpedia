-- Prove2me | Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_summable_shift
-- name    : Formalism.ZF.ComplexPowerDifferenceIntegral.summable_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:56.422659+00:00
-- url     : https://prove2.me/theorems/ebceceac-9f00-4f6e-bf6b-c07377b8d8b4
-- title:
--   Complex Power Difference Integral: summable shift
-- statement:
--   The Complex Power Difference Integral construction uses the summable shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L23-L25

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
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
open Formalism.ZF.ComplexPowerDifferenceIntegral

theorem Formalism.ZF.ComplexPowerDifferenceIntegral.summable_shift {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by sorry
