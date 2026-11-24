-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_mem_H_iff
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.mem_H_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:00.281563+00:00
-- url     : https://prove2.me/theorems/fb60c564-9415-418f-ad20-598dd94c8074
-- title:
--   Principal Injective Common Range: mem H iff
-- statement:
--   The Principal Injective Common Range construction uses the mem H iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L61-L67

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.mem_H_iff {N n : ℕ} (ν : Fin N → ℕ) (P : MvPolynomial (Fin N × Fin n) R) :
    P ∈ H R ν ↔ P.IsWeightedHomogeneous (blockWt N n) ν ∧
      ∀ i j : Fin N, i < j → shear R i j P = Polynomial.C P := by sorry
