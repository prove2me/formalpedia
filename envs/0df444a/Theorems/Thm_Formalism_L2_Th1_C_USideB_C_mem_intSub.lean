-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideB_C_mem_intSub
-- name    : Formalism.L2.Th1.C.USideB.C_mem_intSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:48.993092+00:00
-- url     : https://prove2.me/theorems/bfaccc65-d09f-4b61-bee3-be856fb97563
-- title:
--   USide B: C mem int Sub
-- statement:
--   The USide B construction uses the C mem int Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L179-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L179-L184

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

theorem Formalism.L2.Th1.C.USideB.C_mem_intSub {R : Subring K} {a : K} (ha : a ∈ R) : PowerSeries.C a ∈ intSub R := by sorry
