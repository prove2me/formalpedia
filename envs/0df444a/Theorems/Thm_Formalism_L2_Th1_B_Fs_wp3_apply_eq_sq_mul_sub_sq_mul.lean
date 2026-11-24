-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_wp3_apply_eq_sq_mul_sub_sq_mul
-- name    : Formalism.L2.Th1.B.Fs.wp3_apply_eq_sq_mul_sub_sq_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:12.906803+00:00
-- url     : https://prove2.me/theorems/f6a640b4-bbb0-4863-95c7-fc922dc66ff9
-- title:
--   Fs: wp3 apply eq sq mul sub sq mul
-- statement:
--   The Fs construction uses the wp3 apply eq sq mul sub sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L118-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L118-L127

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

theorem Formalism.L2.Th1.B.Fs.wp3_apply_eq_sq_mul_sub_sq_mul {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) (j k : Fin 3) :
    wp3 P j k = (MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2) *
      fExp (emb j k (par0 (sigS P))) := by sorry
