-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_det_three_points_eq_expansion
-- name    : Formalism.L2.Th1.B.Fs.det_three_points_eq_expansion
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:00.877879+00:00
-- url     : https://prove2.me/theorems/b764c704-6bf6-4335-aae1-f55226953fc2
-- title:
--   Fs: det three points eq expansion
-- statement:
--   The Fs construction uses the det three points eq expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L162-L176

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

theorem Formalism.L2.Th1.B.Fs.det_three_points_eq_expansion (P : PowerSeries K) : det3 P =
    MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * (1 + MvPowerSeries.X 1 ^ 2 * at1 1 P)) *
        (-2 + MvPowerSeries.X 2 ^ 3 * at1 2 (dz P)) -
      MvPowerSeries.X 0 ^ 3 * (-2 + MvPowerSeries.X 1 ^ 3 * at1 1 (dz P)) *
        (MvPowerSeries.X 2 * (1 + MvPowerSeries.X 2 ^ 2 * at1 2 P)) -
      MvPowerSeries.X 0 * (1 + MvPowerSeries.X 0 ^ 2 * at1 0 P) * MvPowerSeries.X 1 ^ 3 *
        (-2 + MvPowerSeries.X 2 ^ 3 * at1 2 (dz P)) +
      MvPowerSeries.X 0 * (1 + MvPowerSeries.X 0 ^ 2 * at1 0 P) *
        (-2 + MvPowerSeries.X 1 ^ 3 * at1 1 (dz P)) * MvPowerSeries.X 2 ^ 3 +
      (-2 + MvPowerSeries.X 0 ^ 3 * at1 0 (dz P)) * MvPowerSeries.X 1 ^ 3 *
        (MvPowerSeries.X 2 * (1 + MvPowerSeries.X 2 ^ 2 * at1 2 P)) -
      (-2 + MvPowerSeries.X 0 ^ 3 * at1 0 (dz P)) *
        (MvPowerSeries.X 1 * (1 + MvPowerSeries.X 1 ^ 2 * at1 1 P)) * MvPowerSeries.X 2 ^ 3 := by sorry
