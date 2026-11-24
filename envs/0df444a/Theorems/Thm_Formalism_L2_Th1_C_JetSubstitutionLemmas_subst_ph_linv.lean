-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_ph_linv
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_ph_linv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:11.35193+00:00
-- url     : https://prove2.me/theorems/db687772-9645-4c28-930c-5d6d6210ddc0
-- title:
--   Jet Substitution Lemmas: subst ph linv
-- statement:
--   The Jet Substitution Lemmas construction uses the subst ph linv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L275-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L275-L279

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

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_ph_linv {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {g : MvPowerSeries σ K} (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (PowerSeries.subst g linv) ph =
      PowerSeries.subst g (PowerSeries.subst linv ph) := by sorry
