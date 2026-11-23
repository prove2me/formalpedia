-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_l_flin
-- name    : Formalism.L2.Th1.C.Pts.l_flin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:53.442799+00:00
-- url     : https://prove2.me/theorems/7cfc777c-9f83-4cb7-b03f-85478ca1d578
-- title:
--   Pts: l flin
-- statement:
--   The Pts construction uses the l flin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L101-L105

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

theorem Formalism.L2.Th1.C.Pts.l_flin (h : IsLogPair l linv) {n : Type} [Fintype n] (c : n → K)
    {u : n → MvPowerSeries σ K} (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    PowerSeries.subst (flin l linv c u) l =
      ∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l := by sorry
