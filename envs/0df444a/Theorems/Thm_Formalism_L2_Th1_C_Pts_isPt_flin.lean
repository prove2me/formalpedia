-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_flin
-- name    : Formalism.L2.Th1.C.Pts.isPt_flin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:53.817016+00:00
-- url     : https://prove2.me/theorems/90f83a70-d8d5-43be-8ce0-083c27122f2c
-- title:
--   Pts: is Pt flin
-- statement:
--   The Pts construction uses the is Pt flin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L402-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L402-L422

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

theorem Formalism.L2.Th1.C.Pts.isPt_flin (h : IsLogPair l linv) (hF : FGInt R l linv) {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ j, EndInt R l linv (c j)) {u : n → MvPowerSeries σ K}
    (hu : ∀ j, IsPt R (u j)) : IsPt R (flin l linv c u) := by sorry
