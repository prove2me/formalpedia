-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Clo_coeffCont_fmul
-- name    : Formalism.L2.Th1.C.Clo.coeffCont_fmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:09.734101+00:00
-- url     : https://prove2.me/theorems/59df08f2-91b0-45f1-8cb1-d287907329fc
-- title:
--   Clo: coeff Cont fmul
-- statement:
--   The Clo construction uses the coeff Cont fmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L105-L109

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {σ : Type}
variable [TopologicalSpace K] [IsTopologicalRing K] {T : Type} [TopologicalSpace T]

theorem Formalism.L2.Th1.C.Clo.coeffCont_fmul {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (linv : PowerSeries K) {c : T → K} (hc : Continuous c) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : CoeffCont fun t => fmul l linv (c t) y := by sorry
