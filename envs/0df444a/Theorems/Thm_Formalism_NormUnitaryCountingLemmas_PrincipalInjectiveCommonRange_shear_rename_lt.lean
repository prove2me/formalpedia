-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_rename_lt
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_lt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:38.738865+00:00
-- url     : https://prove2.me/theorems/14b89e5d-3876-41dd-8c1e-3e2a4c8d2f0b
-- title:
--   Principal Injective Common Range: shear rename lt
-- statement:
--   The Principal Injective Common Range construction uses the shear rename lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L85-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L85-L95

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

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_lt {N N' n : ℕ} (hN : N ≤ N') (i j : Fin N') (hi : (i : ℕ) < N)
    (hj : (j : ℕ) < N) :
    (shear R i j).comp (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) =
      (Polynomial.mapAlgHom (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)))).comp
        (shear R (⟨i, hi⟩ : Fin N) ⟨j, hj⟩) := by sorry
