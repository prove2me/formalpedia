-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_rename_inv
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:38.891397+00:00
-- url     : https://prove2.me/theorems/0f862a01-cb3a-4d32-a76c-fb832e9b15c1
-- title:
--   Principal Injective Common Range: shear rename inv
-- statement:
--   The Principal Injective Common Range construction uses the shear rename inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L108-L120

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

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_inv {N N' n : ℕ} (hN : N ≤ N') (F : MvPolynomial (Fin N × Fin n) R)
    (hF : ∀ i j : Fin N, i < j → shear R i j F = Polynomial.C F) (i j : Fin N') (hij : i < j) :
    shear R i j (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F) =
      Polynomial.C (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F) := by sorry
