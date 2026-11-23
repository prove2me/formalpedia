-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_flin
-- name    : Formalism.L2.Th1.C.Pts.constantCoeff_flin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:50.267219+00:00
-- url     : https://prove2.me/theorems/182e15d3-ca54-4c08-859c-50058a202f4f
-- title:
--   Pts: constant Coeff flin
-- statement:
--   The Pts construction uses the constant Coeff flin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L86-L89

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {l linv : PowerSeries K}

theorem Formalism.L2.Th1.C.Pts.constantCoeff_flin (h : IsLogPair l linv) {n : Type} [Fintype n] (c : n → K)
    {u : n → MvPowerSeries σ K} (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    MvPowerSeries.constantCoeff (flin l linv c u) = 0 := by sorry
