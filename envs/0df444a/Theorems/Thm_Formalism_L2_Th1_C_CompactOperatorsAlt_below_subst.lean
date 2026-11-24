-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_below_subst
-- name    : Formalism.L2.Th1.C.CompactOperatorsAlt.below_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:55.265071+00:00
-- url     : https://prove2.me/theorems/f764460a-8ecd-4725-997d-ac7fb8bfacaa
-- title:
--   Compact Operators Alt: below subst
-- statement:
--   The Compact Operators Alt construction uses the below subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L25-L32

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

theorem Formalism.L2.Th1.C.CompactOperatorsAlt.below_subst {n : ℕ} {A a : PowerSeries K} (hA : IntPS R A)
    (ha0 : constantCoeff a = 0) (ha : ∀ m < n, coeff m a ∈ R) :
    ∀ m < n, coeff m (A.subst a) ∈ R := by sorry
