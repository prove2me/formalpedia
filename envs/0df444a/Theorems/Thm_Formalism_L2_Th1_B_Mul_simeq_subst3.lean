-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Mul_simeq_subst3
-- name    : Formalism.L2.Th1.B.Mul.simeq_subst3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:41.349796+00:00
-- url     : https://prove2.me/theorems/37458c45-f573-5276-97f3-d1d3cc99e4b8
-- title:
--   Mul: simeq subst3
-- statement:
--   The Mul construction uses the simeq subst3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/MultiplicationBiadditiveHolds.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/MultiplicationBiadditiveHolds.lean#L229-L235

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Mul
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}

theorem Formalism.L2.Th1.B.Mul.simeq_subst3 {q : MvPowerSeries (Fin 3) K} (hq : Simeq q 0) (U V W : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (hW : MvPowerSeries.constantCoeff W = 0) (iU : Integral U) (iV : Integral V)
    (iW : Integral W) : Simeq (MvPowerSeries.subst ![U, V, W] q) 0 := by sorry
