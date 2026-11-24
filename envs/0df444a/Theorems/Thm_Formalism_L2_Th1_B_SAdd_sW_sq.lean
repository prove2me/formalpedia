-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_SAdd_sW_sq
-- name    : Formalism.L2.Th1.B.SAdd.sW_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:02:15.910987+00:00
-- url     : https://prove2.me/theorems/de14719d-d49a-454a-9a36-b9702fb3eaed
-- title:
--   SAdd: s W sq
-- statement:
--   The SAdd construction uses the s W sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L38-L47

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
open PowerSeries
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.SAdd.sW_sq {w : PowerSeries K} (h0 : constantCoeff w = 0) (h1 : coeff 1 w = 0)
    (h2 : coeff 2 w = 1) : sW w ^ 2 = w := by sorry
