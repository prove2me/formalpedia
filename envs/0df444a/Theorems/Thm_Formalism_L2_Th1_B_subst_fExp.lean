-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_subst_fExp
-- name    : Formalism.L2.Th1.B.subst_fExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:13.710689+00:00
-- url     : https://prove2.me/theorems/929ff30c-0fe4-4453-9e02-6d1820a73d48
-- title:
--   B: subst f Exp
-- statement:
--   The B construction uses the subst f Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/OneAddMulDerivLogSubst.lean#L271-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/OneAddMulDerivLogSubst.lean#L271-L275

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem Formalism.L2.Th1.B.subst_fExp {κ : Type} [Finite ι] {φ : ι → MvPowerSeries κ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst φ (fExp f) = fExp (MvPowerSeries.subst φ f) := by sorry
