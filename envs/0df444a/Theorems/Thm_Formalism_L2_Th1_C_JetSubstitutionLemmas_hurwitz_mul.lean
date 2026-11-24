-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hurwitz_mul
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.hurwitz_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.492587+00:00
-- url     : https://prove2.me/theorems/59e2076f-01db-4262-8133-e63f97f2d421
-- title:
--   Jet Substitution Lemmas: hurwitz mul
-- statement:
--   The Jet Substitution Lemmas construction uses the hurwitz mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L399-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L399-L414

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

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.hurwitz_mul {A B : PowerSeries K} (n : ℕ)
    (hA : ∀ j ≤ n, (j.factorial : K) * PowerSeries.coeff j A ∈ R)
    (hB : ∀ k ≤ n, (k.factorial : K) * PowerSeries.coeff k B ∈ R) :
    (n.factorial : K) * PowerSeries.coeff n (A * B) ∈ R := by sorry
