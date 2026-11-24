-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_of_sq
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_of_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:58.677934+00:00
-- url     : https://prove2.me/theorems/ef81b419-9137-4564-b0ce-1a9b993a58aa
-- title:
--   Integral Mv Polynomial Lemmas: int Mv of sq
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the int Mv of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L152-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L152-L182

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

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_of_sq {g : MvPowerSeries σ K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : MvPowerSeries.constantCoeff g = 1) (hgg : IntMv R (g * g)) : IntMv R g := by sorry
