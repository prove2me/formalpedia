-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_addDefect_eq
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.addDefect_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:19.651968+00:00
-- url     : https://prove2.me/theorems/d3ac18e4-9272-4fe7-b8e7-80e380541a05
-- title:
--   Jet Substitution Lemmas: add Defect eq
-- statement:
--   The Jet Substitution Lemmas construction uses the add Defect eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L335-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L335-L353

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
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.addDefect_eq {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K) (a b : K) :
    be0 l linv ph (fmul l linv a (MvPowerSeries.X (0 : Fin 2)))
        (fmul l linv b (MvPowerSeries.X (1 : Fin 2))) =
      Q l (PowerSeries.subst linv ph) a b - Q l (PowerSeries.subst linv ph) a 0 -
        Q l (PowerSeries.subst linv ph) 0 b := by sorry
