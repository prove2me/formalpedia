-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_pderiv_series_at_difference_three
-- name    : Formalism.L2.Th1.B.Fs.pderiv_series_at_difference_three
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:15.109513+00:00
-- url     : https://prove2.me/theorems/086c83a1-2d21-44d5-82c7-a5fcd72ebece
-- title:
--   Fs: pderiv series at difference three
-- statement:
--   The Fs construction uses the pderiv series at difference three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L270-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L270-L273

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

theorem Formalism.L2.Th1.B.Fs.pderiv_series_at_difference_three (i j k : Fin 3) (f : PowerSeries K) :
    MvPowerSeries.pderiv K i (evalDiffThree j k f : A3) =
      evalDiffThree j k (dz f) * ((if j = i then 1 else 0) - if k = i then 1 else 0) := by sorry
