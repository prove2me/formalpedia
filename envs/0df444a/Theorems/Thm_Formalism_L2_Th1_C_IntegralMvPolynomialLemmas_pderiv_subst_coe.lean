-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_subst_coe
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_subst_coe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:45.967417+00:00
-- url     : https://prove2.me/theorems/14ec9d0f-9aac-416b-83c0-577ee22af5cc
-- title:
--   Integral Mv Polynomial Lemmas: pderiv subst coe
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the pderiv subst coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L30-L35

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
variable {A : Type*} [CommRing A] {σ : Type*}

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_subst_coe (p : Polynomial A) {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv A i ((p : PowerSeries A).subst a) =
      (derivative A (p : PowerSeries A)).subst a * MvPowerSeries.pderiv A i a := by sorry
