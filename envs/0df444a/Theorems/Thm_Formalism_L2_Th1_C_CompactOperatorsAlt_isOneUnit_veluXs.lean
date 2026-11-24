-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_isOneUnit_veluXs
-- name    : Formalism.L2.Th1.C.CompactOperatorsAlt.isOneUnit_veluXs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:54.36586+00:00
-- url     : https://prove2.me/theorems/8982eb59-f23f-4d27-b40c-0d4dd6cf64b3
-- title:
--   Compact Operators Alt: is One Unit velu Xs
-- statement:
--   The Compact Operators Alt construction uses the is One Unit velu Xs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L94-L100

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
variable {K : Type} [Field K] {R : Subring K}

theorem Formalism.L2.Th1.C.CompactOperatorsAlt.isOneUnit_veluXs {A : PowerSeries K} {ι : Type} [Fintype ι] {xs : ι → PowerSeries K}
    {xP : ι → K} {r : K} (hA : IsOneUnit R A) (hxs : ∀ P, IntPS R (xs P)) (hxP : ∀ P, xP P ∈ R)
    (hr : r ∈ R) : IsOneUnit R (veluXs A xs xP r) := by sorry
