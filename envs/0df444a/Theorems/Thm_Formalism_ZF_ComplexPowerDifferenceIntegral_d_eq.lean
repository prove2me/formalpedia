-- Prove2me | Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_d_eq
-- name    : Formalism.ZF.ComplexPowerDifferenceIntegral.d_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:58.019068+00:00
-- url     : https://prove2.me/theorems/de2bef00-376e-4425-9983-f05169c90ea9
-- title:
--   Complex Power Difference Integral: d eq
-- statement:
--   The Complex Power Difference Integral construction uses the d eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean#L59-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean#L59-L78

import Mathlib
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
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

theorem Formalism.ZF.ComplexPowerDifferenceIntegral.d_eq {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (a : ℂ) ^ (1 - s) - ((a + 1 : ℝ) : ℂ) ^ (1 - s) - (s - 1) * ((a + 1 : ℝ) : ℂ) ^ (-s) =
      (s - 1) * eint s a := by sorry
