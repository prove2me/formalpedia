-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_fExp_three
-- name    : Formalism.L2.Th1.B.Fs.fExp_three
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:44.370814+00:00
-- url     : https://prove2.me/theorems/8dac496c-4023-4f6b-88a4-a41c5a15af1b
-- title:
--   Fs: f Exp three
-- statement:
--   The Fs construction uses the f Exp three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L361-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L361-L365

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

theorem Formalism.L2.Th1.B.Fs.fExp_three {K : Type} [Field K] [CharZero K] {ι : Type} {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : fExp f ^ 3 = fExp (3 * f) := by sorry
