-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_coeff_of_sq
-- name    : Formalism.L2.Th1.C.CompactOperatorsAlt.coeff_of_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:47.114104+00:00
-- url     : https://prove2.me/theorems/ebb2a2fd-ccc3-40c3-8c17-c465adc1ad75
-- title:
--   Compact Operators Alt: coeff of sq
-- statement:
--   The Compact Operators Alt construction uses the coeff of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L43-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralEndomorphismFromDatum.lean#L43-L68

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

theorem Formalism.L2.Th1.C.CompactOperatorsAlt.coeff_of_sq {n : ℕ} {g : PowerSeries K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : constantCoeff g = 1) (hg : ∀ m < n, coeff m g ∈ R) (hgg : coeff n (g * g) ∈ R) :
    coeff n g ∈ R := by sorry
