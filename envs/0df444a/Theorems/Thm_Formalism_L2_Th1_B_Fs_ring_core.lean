-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_ring_core
-- name    : Formalism.L2.Th1.B.Fs.ring_core
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:41.175091+00:00
-- url     : https://prove2.me/theorems/1efd54b2-084b-43d3-9623-f0f62680c9f9
-- title:
--   Fs: ring core
-- statement:
--   The Fs construction uses the ring core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L301-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L301-L314

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Add0_ring_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K

theorem Formalism.L2.Th1.B.Fs.ring_core {R : Type} [CommRing R] (a b c M01 M02 M12 D01 D02 D12 t01 t02 t12 A DA : R)
    (T01 : (a - b) * D01 = M01 * (2 + 2 * (a - b) * t01))
    (T02 : (a - c) * D02 = M02 * (2 + 2 * (a - c) * t02))
    (T12 : (b - c) * D12 = M12 * (2 + 2 * (b - c) * t12))
    (hR : 2 * M01 * M02 * M12 * DA =
      A * (-D01 * M02 * M12 + D02 * M01 * M12 + 2 * D12 * M01 * M02)) :
    (2 * M01 * M02 * M12) *
        (A * ((a + b + c) * (-((a - c) * (b - c)) + (a - b) * (b - c) + 2 * ((a - b) * (a - c))) +
          (a + b + c) * (a - b) * (a - c) * (b - c) * (-t01 + t02 + 2 * t12))) =
      (2 * M01 * M02 * M12) * ((a + b + c) * (a - b) * (a - c) * (b - c) * DA) := by sorry
