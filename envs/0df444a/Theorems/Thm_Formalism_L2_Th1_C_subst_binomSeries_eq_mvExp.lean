-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_subst_binomSeries_eq_mvExp
-- name    : Formalism.L2.Th1.C.subst_binomSeries_eq_mvExp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:53.165749+00:00
-- url     : https://prove2.me/theorems/1a55d499-b65b-4a38-a5bc-990a8af0fa48
-- title:
--   C: subst binom Series eq mv Exp
-- statement:
--   The C construction uses the subst binom Series eq mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffSubstBinomSeries.lean#L72-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffSubstBinomSeries.lean#L72-L106

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffSubstBinomSeries
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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem Formalism.L2.Th1.C.subst_binomSeries_eq_mvExp (z : K) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (mvExp f - 1) (binomSeries z) = mvExp (z • f) := by sorry
