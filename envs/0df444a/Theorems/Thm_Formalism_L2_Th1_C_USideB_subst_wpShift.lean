-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideB_subst_wpShift
-- name    : Formalism.L2.Th1.C.USideB.subst_wpShift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:31.264518+00:00
-- url     : https://prove2.me/theorems/9d07cea2-a540-4068-9dd1-8b49f703285a
-- title:
--   USide B: subst wp Shift
-- statement:
--   The USide B construction uses the subst wp Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L49-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideB.lean#L49-L63

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

theorem Formalism.L2.Th1.C.USideB.subst_wpShift {e l A : PowerSeries K} {c0 : K} (hl : PowerSeries.constantCoeff l = 0)
    (hX : XIsWp e l A c0) (x : K) :
    PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e (x + c0)) =
      (A - PowerSeries.C x * PowerSeries.X ^ 2) * l ^ 2 := by sorry
