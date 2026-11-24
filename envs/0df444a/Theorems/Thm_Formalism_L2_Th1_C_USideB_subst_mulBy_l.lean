-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideB_subst_mulBy_l
-- name    : Formalism.L2.Th1.C.USideB.subst_mulBy_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:28.661659+00:00
-- url     : https://prove2.me/theorems/e546e76c-a313-4f0f-bff4-26ce19218876
-- title:
--   USide B: subst mul By l
-- statement:
--   The USide B construction uses the subst mul By l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L28-L32

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
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.C.USideB.subst_mulBy_l {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.subst (mulBy l linv al) l = PowerSeries.C al * l := by sorry
