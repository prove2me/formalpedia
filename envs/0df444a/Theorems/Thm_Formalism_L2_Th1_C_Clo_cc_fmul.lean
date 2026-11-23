-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_fmul
-- name    : Formalism.L2.Th1.C.Clo.cc_fmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:43.375833+00:00
-- url     : https://prove2.me/theorems/6e5604dd-1ce0-43c3-a55a-6a92e2a67ff4
-- title:
--   Clo: cc fmul
-- statement:
--   The Clo construction uses the cc fmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L111-L115

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

theorem Formalism.L2.Th1.C.Clo.cc_fmul {l linv : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hli : PowerSeries.constantCoeff linv = 0) (a : K) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (fmul l linv a y) = 0 := by sorry
