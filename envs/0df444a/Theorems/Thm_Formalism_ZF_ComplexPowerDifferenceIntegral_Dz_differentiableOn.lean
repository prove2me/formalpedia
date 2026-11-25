-- Prove2me | Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_Dz_differentiableOn
-- name    : Formalism.ZF.ComplexPowerDifferenceIntegral.Dz_differentiableOn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:40.590498+00:00
-- url     : https://prove2.me/theorems/888b805e-8eb8-4b02-9145-ab33f98d2341
-- title:
--   Complex Power Difference Integral: Dz differentiable On
-- statement:
--   The Complex Power Difference Integral construction uses the Dz differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L31-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L31-L75

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

theorem Formalism.ZF.ComplexPowerDifferenceIntegral.Dz_differentiableOn : DifferentiableOn ℂ Dz {s : ℂ | 0 < s.re} := by sorry
