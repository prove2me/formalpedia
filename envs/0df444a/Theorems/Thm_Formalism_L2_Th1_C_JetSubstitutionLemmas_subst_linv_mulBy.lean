-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_linv_mulBy
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_linv_mulBy
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:27.525541+00:00
-- url     : https://prove2.me/theorems/f916d245-b150-4962-b6ce-ad0f5b4f7ff3
-- title:
--   Jet Substitution Lemmas: subst linv mul By
-- statement:
--   The Jet Substitution Lemmas construction uses the subst linv mul By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L195-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L195-L210

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
open JetSubstitutionLemmas
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_linv_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K)
    (ph : PowerSeries K) :
    PowerSeries.subst linv (PowerSeries.subst (mulBy l linv a) ph) =
      PowerSeries.rescale a (PowerSeries.subst linv ph) := by sorry
