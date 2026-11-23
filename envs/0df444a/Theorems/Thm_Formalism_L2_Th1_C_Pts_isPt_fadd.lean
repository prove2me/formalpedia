-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fadd
-- name    : Formalism.L2.Th1.C.Pts.isPt_fadd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:49.037071+00:00
-- url     : https://prove2.me/theorems/cdf2de96-160c-4ced-beab-644a5db0a7bb
-- title:
--   Pts: is Pt fadd
-- statement:
--   The Pts construction uses the is Pt fadd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L223-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L223-L230

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
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}

theorem Formalism.L2.Th1.C.Pts.isPt_fadd (h : IsLogPair l linv) (hF : FGInt R l linv) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) : IsPt R (fadd l linv x y) := by sorry
