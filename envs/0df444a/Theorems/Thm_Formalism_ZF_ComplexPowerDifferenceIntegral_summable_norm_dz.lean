-- Prove2me | Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_summable_norm_dz
-- name    : Formalism.ZF.ComplexPowerDifferenceIntegral.summable_norm_dz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:30.864108+00:00
-- url     : https://prove2.me/theorems/b68db663-f668-4f7d-bc2d-9f96f15d630b
-- title:
--   Complex Power Difference Integral: summable norm dz
-- statement:
--   The Complex Power Difference Integral construction uses the summable norm dz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L27-L29

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

theorem Formalism.ZF.ComplexPowerDifferenceIntegral.summable_norm_dz {s : ℂ} (hs : 0 < s.re) : Summable (fun n => ‖dz s n‖) := by sorry
