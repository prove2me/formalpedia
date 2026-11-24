-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_int_of_eq
-- name    : Formalism.L2.Th1.C.CompactOperatorsAlt.int_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:05.334844+00:00
-- url     : https://prove2.me/theorems/2517dc8f-7ffb-433e-a891-53611f23d988
-- title:
--   Compact Operators Alt: int of eq
-- statement:
--   The Compact Operators Alt construction uses the int of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L70-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L70-L92

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

theorem Formalism.L2.Th1.C.CompactOperatorsAlt.int_of_eq {A V g : PowerSeries K} {al : K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hA : IntPS R A) (hV : IsOneUnit R V) (hal : al ∈ R) (hg0 : constantCoeff g = 1)
    (hEq : A.subst (C al * X * g) = g * g * V) : IntPS R g := by sorry
