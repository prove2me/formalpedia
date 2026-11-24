-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideB_mvExp_pow
-- name    : Formalism.L2.Th1.C.USideB.mvExp_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:25.482543+00:00
-- url     : https://prove2.me/theorems/1ffeae81-cc00-464a-a677-e003c7642617
-- title:
--   USide B: mv Exp pow
-- statement:
--   The USide B construction uses the mv Exp pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L71-L81

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.C.USideB.mvExp_pow (hE : MvExpLaws) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0)
    (m : ℕ) : (mvExp f : PowerSeries K) ^ m = mvExp ((m : K) • f) := by sorry
