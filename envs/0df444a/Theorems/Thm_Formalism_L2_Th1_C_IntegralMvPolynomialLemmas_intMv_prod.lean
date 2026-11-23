-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_prod
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:23.308815+00:00
-- url     : https://prove2.me/theorems/25856f61-a735-4b46-a0b3-3a8c46121ac6
-- title:
--   Integral Mv Polynomial Lemmas: int Mv prod
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the int Mv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L106-L108

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
variable {K : Type} [Field K] {σ : Type} {R : Subring K}

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_prod {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries σ K}
    (hF : ∀ i ∈ s, IntMv R (F i)) : IntMv R (∏ i ∈ s, F i) := by sorry
