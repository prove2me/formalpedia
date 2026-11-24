-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_E2_curve3_at
-- name    : Formalism.L2.Th1.B.E2.curve3_at
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:48.626197+00:00
-- url     : https://prove2.me/theorems/afa7673d-880d-4ff3-b569-edc08c373d23
-- title:
--   E2: curve3 at
-- statement:
--   The E2 construction uses the curve3 at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L143-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L143-L158

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.E2.curve3_at {ι : Type} {l P ep : PowerSeries K} {a1 a3 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative K P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3)) (x : ι) :
    MvPowerSeries.X x ^ 3 * (-2 + at1 x l ^ 3 * PowerSeries.subst (at1 x l) (dz P)) =
      at1 x l ^ 3 * (-2 * at1 x ep + MvPowerSeries.C a1 * MvPowerSeries.X x * at1 x ep +
        MvPowerSeries.C a3 * MvPowerSeries.X x ^ 3) := by sorry
