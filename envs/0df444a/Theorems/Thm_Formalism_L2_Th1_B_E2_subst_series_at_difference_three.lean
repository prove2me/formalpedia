-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_E2_subst_series_at_difference_three
-- name    : Formalism.L2.Th1.B.E2.subst_series_at_difference_three
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:14.348818+00:00
-- url     : https://prove2.me/theorems/2f4edea5-ad10-4b34-a0c3-26be9a8c4ee5
-- title:
--   E2: subst series at difference three
-- statement:
--   The E2 construction uses the subst series at difference three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L185-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L185-L193

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

theorem Formalism.L2.Th1.B.E2.subst_series_at_difference_three {ι : Type} (j k : Fin 3) (g : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (evalDiffThree j k g) = PowerSeries.subst (b j - b k) g := by sorry
