-- Prove2me | Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_norm_dz_le
-- name    : Formalism.ZF.ComplexPowerDifferenceIntegral.norm_dz_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:31.905788+00:00
-- url     : https://prove2.me/theorems/5aacb273-2466-4e2b-a229-a1f0db727eef
-- title:
--   Complex Power Difference Integral: norm dz le
-- statement:
--   The Complex Power Difference Integral construction uses the norm dz le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean#L17-L21

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

theorem Formalism.ZF.ComplexPowerDifferenceIntegral.norm_dz_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by sorry
