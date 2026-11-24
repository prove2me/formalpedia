-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_D_fsE
-- name    : Formalism.L2.Th1.B.Fs.D_fsE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:53.950048+00:00
-- url     : https://prove2.me/theorems/e144af8e-3d7c-43b1-927b-e918d92b9191
-- title:
--   Fs: D fs E
-- statement:
--   The Fs construction uses the D fs E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L292-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L292-L299

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
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

theorem Formalism.L2.Th1.B.Fs.D_fsE (f : PowerSeries K) : pd 1 (fsE f) - pd 2 (fsE f) =
    -(evalDiffThree 0 1 (dz f) - at1 0 (dz f) + at1 1 (dz f)) +
      (evalDiffThree 0 2 (dz f) - at1 0 (dz f) + at1 2 (dz f)) +
      2 * (evalDiffThree 1 2 (dz f) - at1 1 (dz f) + at1 2 (dz f)) := by sorry
