-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_subst
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:56.824797+00:00
-- url     : https://prove2.me/theorems/6aaee3d8-1b4b-4248-8465-d9fbe16feffa
-- title:
--   Integral Mv Polynomial Lemmas: int Mv subst
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the int Mv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L116-L122

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

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_subst {c : PowerSeries K} (hc : IntPS R c) {a : MvPowerSeries σ K}
    (ha : IsPt R a) : IntMv R (c.subst a) := by sorry
