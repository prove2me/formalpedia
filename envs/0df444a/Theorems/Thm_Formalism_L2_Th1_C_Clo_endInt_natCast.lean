-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Clo_endInt_natCast
-- name    : Formalism.L2.Th1.C.Clo.endInt_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:37.371612+00:00
-- url     : https://prove2.me/theorems/274c8d7d-2e72-4bc2-9ca2-36be309a28e0
-- title:
--   Clo: end Int nat Cast
-- statement:
--   The Clo construction uses the end Int nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L204-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L204-L208

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

theorem Formalism.L2.Th1.C.Clo.endInt_natCast (h : IsLogPair l linv) (hF : FGInt R l linv) (n : ℕ) :
    EndInt R l linv (n : K) := by sorry
