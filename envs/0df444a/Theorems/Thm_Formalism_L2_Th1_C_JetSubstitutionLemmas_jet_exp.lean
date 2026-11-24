-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_exp
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.jet_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:50.753537+00:00
-- url     : https://prove2.me/theorems/aa2070b7-2bdd-419a-935c-fd413ee476a6
-- title:
--   Jet Substitution Lemmas: jet exp
-- statement:
--   The Jet Substitution Lemmas construction uses the jet exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L440-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L440-L452

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
variable {K : Type} [Field K] {R : Subring K}
variable [CharZero K]

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.jet_exp {l linv F : PowerSeries K} (h : IsLogPair l linv)
    (hF0 : PowerSeries.constantCoeff F = 0) (hF : ∀ i : ℕ, 1 ≤ i → jet l F i ∈ R) (i : ℕ) :
    jet l (mvExp F : PowerSeries K) i ∈ R := by sorry
