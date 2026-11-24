-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideB_int_of_mul
-- name    : Formalism.L2.Th1.C.USideB.int_of_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:51.959247+00:00
-- url     : https://prove2.me/theorems/56eae712-6377-4d59-ab0f-16b775665f4e
-- title:
--   USide B: int of mul
-- statement:
--   The USide B construction uses the int of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L193-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L193-L211

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
open USideB
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.C.USideB.int_of_mul {R : Subring K} {U V W : PowerSeries K} (hU : IsOneUnit R U) (hW : IntPS R W)
    (h : V * U = W) : IntPS R V := by sorry
