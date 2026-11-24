-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_SAdd_atS_sq
-- name    : Formalism.L2.Th1.B.SAdd.atS_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:02:01.257909+00:00
-- url     : https://prove2.me/theorems/6a002497-a294-4e7c-9047-da8a5e08b6db
-- title:
--   SAdd: at S sq
-- statement:
--   The SAdd construction uses the at S sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L132-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L132-L136

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
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.SAdd.atS_sq (f : PowerSeries K) : atS (f ^ 2) = atS f ^ 2 := by sorry
