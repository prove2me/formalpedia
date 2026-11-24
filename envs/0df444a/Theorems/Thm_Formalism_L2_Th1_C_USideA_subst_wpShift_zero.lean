-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideA_subst_wpShift_zero
-- name    : Formalism.L2.Th1.C.USideA.subst_wpShift_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:04.710688+00:00
-- url     : https://prove2.me/theorems/8ab45490-2021-402b-b255-9a333ba11d03
-- title:
--   USide A: subst wp Shift zero
-- statement:
--   The USide A construction uses the subst wp Shift zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L131-L136

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.C.USideA.subst_wpShift_zero {a : PowerSeries K} (ha : PowerSeries.HasSubst a) (e : PowerSeries K) :
    PowerSeries.subst a (wpShift e 0) = 1 + a ^ 2 * PowerSeries.subst a e := by sorry
