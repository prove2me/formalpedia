-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_fmul_neg
-- name    : Formalism.L2.Th1.C.Pts.fadd_fmul_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:46.002816+00:00
-- url     : https://prove2.me/theorems/cbf69c2b-c485-4058-8389-befd5b382af9
-- title:
--   Pts: fadd fmul neg
-- statement:
--   The Pts construction uses the fadd fmul neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L155-L158

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

theorem Formalism.L2.Th1.C.Pts.fadd_fmul_neg (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fadd l linv (fmul l linv a x) (fmul l linv (-a) x) = 0 := by sorry
