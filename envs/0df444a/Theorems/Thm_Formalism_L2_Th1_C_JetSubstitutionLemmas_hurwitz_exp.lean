-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hurwitz_exp
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.hurwitz_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:16.438907+00:00
-- url     : https://prove2.me/theorems/f60ee05d-1494-4cb3-9118-3552b4efe99d
-- title:
--   Jet Substitution Lemmas: hurwitz exp
-- statement:
--   The Jet Substitution Lemmas construction uses the hurwitz exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L425-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L425-L438

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

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.hurwitz_exp {F : PowerSeries K} (hF0 : PowerSeries.constantCoeff F = 0)
    (hF : ∀ i : ℕ, 1 ≤ i → (i.factorial : K) * PowerSeries.coeff i F ∈ R) (n : ℕ) :
    (n.factorial : K) * PowerSeries.coeff n (mvExp F : PowerSeries K) ∈ R := by sorry
