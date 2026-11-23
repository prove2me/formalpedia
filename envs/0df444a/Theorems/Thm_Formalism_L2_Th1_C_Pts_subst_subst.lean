-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst
-- name    : Formalism.L2.Th1.C.Pts.subst_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:41.02627+00:00
-- url     : https://prove2.me/theorems/1e3ff246-c0e5-44cd-89fc-b6ad2c5f88ea
-- title:
--   Pts: subst subst
-- statement:
--   The Pts construction uses the subst subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L20-L24

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

theorem Formalism.L2.Th1.C.Pts.subst_subst {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0)
    {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) (f : PowerSeries K) :
    PowerSeries.subst x (PowerSeries.subst g f) = PowerSeries.subst (PowerSeries.subst x g) f := by sorry
