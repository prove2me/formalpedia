-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_derivative_of_LG
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_derivative_of_LG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:47.770016+00:00
-- url     : https://prove2.me/theorems/27b6b688-9beb-49ff-815a-f2deed3322ca
-- title:
--   Jet Substitution Lemmas: int PS derivative of LG
-- statement:
--   The Jet Substitution Lemmas construction uses the int PS derivative of LG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L144-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L144-L155

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K] [CharZero K] {R : Subring K}

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_derivative_of_LG {f : PowerSeries K} (hf : LG R f) :
    IntPS R (PowerSeries.derivative K f) := by sorry
