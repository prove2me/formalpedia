-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideB_subst_rescale
-- name    : Formalism.L2.Th1.C.USideB.subst_rescale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:24.467992+00:00
-- url     : https://prove2.me/theorems/11f75b41-f43b-4820-9978-9fa5307b57d5
-- title:
--   USide B: subst rescale
-- statement:
--   The USide B construction uses the subst rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L34-L41

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

theorem Formalism.L2.Th1.C.USideB.subst_rescale {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    PowerSeries.subst l (PowerSeries.rescale al g) =
      PowerSeries.subst (mulBy l linv al) (PowerSeries.subst l g) := by sorry
