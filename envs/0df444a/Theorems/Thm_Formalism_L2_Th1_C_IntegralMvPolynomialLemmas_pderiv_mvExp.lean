-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_mvExp
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:30.928417+00:00
-- url     : https://prove2.me/theorems/4ea289e4-e9ed-4ce8-a05e-b52eff2e823d
-- title:
--   Integral Mv Polynomial Lemmas: pderiv mv Exp
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the pderiv mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L202-L205

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

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (i : σ) :
    MvPowerSeries.pderiv K i (mvExp f) = mvExp f * MvPowerSeries.pderiv K i f := by sorry
