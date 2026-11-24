-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_D_vand3
-- name    : Formalism.L2.Th1.B.Fs.D_vand3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:49.503521+00:00
-- url     : https://prove2.me/theorems/ed6367ac-fa72-4a52-abc4-cb0b3f708171
-- title:
--   Fs: D vand3
-- statement:
--   The Fs construction uses the D vand3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L283-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L283-L290

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

theorem Formalism.L2.Th1.B.Fs.D_vand3 : pd 1 (vand3 K) - pd 2 (vand3 K) =
    (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
      (-((MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2)) +
        (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) +
        2 * ((MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2))) := by sorry
