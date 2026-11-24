-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Clo_zLin_natCast
-- name    : Formalism.L2.Th1.C.Clo.zLin_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:53.502434+00:00
-- url     : https://prove2.me/theorems/7ba580cf-9011-4f85-b2d6-d92fa78ed024
-- title:
--   Clo: z Lin nat Cast
-- statement:
--   The Clo construction uses the z Lin nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L224-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L224-L236

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
open Clo
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {R : Subring K} {l linv : PowerSeries K}
variable [CharZero K] {ph : PowerSeries K} {σ : Type}

theorem Formalism.L2.Th1.C.Clo.zLin_natCast (h : Frame R l linv ph) (h1 : F1 R l linv ph) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) (n : ℕ) :
    LG R (be0 l linv ph x (fmul l linv (n : K) y) - (n : K) • be0 l linv ph x y) := by sorry
