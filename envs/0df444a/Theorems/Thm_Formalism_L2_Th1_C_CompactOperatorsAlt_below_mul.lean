-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_below_mul
-- name    : Formalism.L2.Th1.C.CompactOperatorsAlt.below_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:55.481794+00:00
-- url     : https://prove2.me/theorems/55ced7c1-41fb-4f91-aa65-a469936c513f
-- title:
--   Compact Operators Alt: below mul
-- statement:
--   The Compact Operators Alt construction uses the below mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L17-L23

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

theorem Formalism.L2.Th1.C.CompactOperatorsAlt.below_mul {n : ℕ} {f h : PowerSeries K} (hf : ∀ m < n, coeff m f ∈ R)
    (hh : ∀ m < n, coeff m h ∈ R) : ∀ m < n, coeff m (f * h) ∈ R := by sorry
