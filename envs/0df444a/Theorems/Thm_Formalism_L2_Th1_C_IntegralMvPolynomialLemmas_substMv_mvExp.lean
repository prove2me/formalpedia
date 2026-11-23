-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_substMv_mvExp
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:21.908805+00:00
-- url     : https://prove2.me/theorems/26dc98cc-5787-4965-a46b-06dec896b9f6
-- title:
--   Integral Mv Polynomial Lemmas: subst Mv mv Exp
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the subst Mv mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L207-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L207-L214

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
variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp {τ : Type} [Finite σ] {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by sorry
