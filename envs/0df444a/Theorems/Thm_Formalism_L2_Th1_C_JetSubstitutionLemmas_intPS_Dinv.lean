-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_Dinv
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_Dinv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:14.983609+00:00
-- url     : https://prove2.me/theorems/cad9a225-5cd9-4451-8759-ba77dcbaec9e
-- title:
--   Jet Substitution Lemmas: int PS Dinv
-- statement:
--   The Jet Substitution Lemmas construction uses the int PS Dinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L132-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L132-L136

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
variable {K : Type} [Field K]
variable {R : Subring K}

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_Dinv {l f : PowerSeries K} (hl : IsOneUnit R (PowerSeries.derivative K l))
    (hf : IntPS R (PowerSeries.derivative K f)) : IntPS R (Dinv l f) := by sorry
