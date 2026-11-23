-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst
-- name    : Formalism.L2.Th1.C.Pts.substMv_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:28.886874+00:00
-- url     : https://prove2.me/theorems/65767967-2cc7-4a08-971b-298b3822d171
-- title:
--   Pts: subst Mv subst
-- statement:
--   The Pts construction uses the subst Mv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L26-L33

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

theorem Formalism.L2.Th1.C.Pts.substMv_subst {τ : Type} [Finite σ] {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) =
      PowerSeries.subst (MvPowerSeries.subst a g) f := by sorry
