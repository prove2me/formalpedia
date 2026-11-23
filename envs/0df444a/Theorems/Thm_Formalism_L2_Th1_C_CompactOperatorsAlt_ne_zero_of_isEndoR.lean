-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_ne_zero_of_isEndoR
-- name    : Formalism.L2.Th1.C.CompactOperatorsAlt.ne_zero_of_isEndoR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:02.639021+00:00
-- url     : https://prove2.me/theorems/24a36eab-a518-4cff-a32e-f9f092aee997
-- title:
--   Compact Operators Alt: ne zero of is Endo R
-- statement:
--   The Compact Operators Alt construction uses the ne zero of is Endo R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L129-L133

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
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
open Formalism.L2.Th1.C.CompactOperatorsAlt

theorem Formalism.L2.Th1.C.CompactOperatorsAlt.ne_zero_of_isEndoR {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {al albar : K}
    (hN : al * albar = (Fintype.card ι : K) + 1) : al ≠ 0 := by sorry
