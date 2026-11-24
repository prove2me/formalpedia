-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_vandermonde_three
-- name    : Formalism.L2.Th1.B.Fs.eval_last_zero_vandermonde_three
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:37.718735+00:00
-- url     : https://prove2.me/theorems/2ebf581c-cf25-4a88-bbf4-7e1699bd5d3e
-- title:
--   Fs: eval last zero vandermonde three
-- statement:
--   The Fs construction uses the eval last zero vandermonde three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L185-L188

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

theorem Formalism.L2.Th1.B.Fs.eval_last_zero_vandermonde_three : ev3H (vand3 K) =
    (MvPowerSeries.X 0 * MvPowerSeries.X 1) * (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) := by sorry
