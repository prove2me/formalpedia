-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Clo_isClosed_LG
-- name    : Formalism.L2.Th1.C.Clo.isClosed_LG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:38.437701+00:00
-- url     : https://prove2.me/theorems/62f78883-2029-491b-b33b-4cc62bae9326
-- title:
--   Clo: is Closed LG
-- statement:
--   The Clo construction uses the is Closed LG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L87-L94

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

theorem Formalism.L2.Th1.C.Clo.isClosed_LG [CharZero K] {R : Subring K} (hR : IsClosed (R : Set K))
    {f : T → MvPowerSeries σ K} (hf : CoeffCont f)
    (h0 : ∀ t, MvPowerSeries.constantCoeff (f t) = 0) : IsClosed {t | LG R (f t)} := by sorry
