-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideB_X_mem_intSub
-- name    : Formalism.L2.Th1.C.USideB.X_mem_intSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:39.153807+00:00
-- url     : https://prove2.me/theorems/3e3221f4-af47-427d-8f31-8549aaa792b4
-- title:
--   USide B: X mem int Sub
-- statement:
--   The USide B construction uses the X mem int Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L186-L191

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

theorem Formalism.L2.Th1.C.USideB.X_mem_intSub (R : Subring K) : (PowerSeries.X : PowerSeries K) ∈ intSub R := by sorry
