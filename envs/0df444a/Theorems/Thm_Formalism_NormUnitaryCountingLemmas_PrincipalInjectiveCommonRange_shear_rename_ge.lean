-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_rename_ge
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_ge
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:56.495938+00:00
-- url     : https://prove2.me/theorems/12748932-1922-43e2-adf2-e9a3970456a9
-- title:
--   Principal Injective Common Range: shear rename ge
-- statement:
--   The Principal Injective Common Range construction uses the shear rename ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L97-L106

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

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_rename_ge {N N' n : ℕ} (hN : N ≤ N') (i j : Fin N') (hj : N ≤ (j : ℕ)) :
    (shear R i j).comp (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) =
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin N' × Fin n) R)
        (Polynomial (MvPolynomial (Fin N' × Fin n) R))).comp
        (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2))) := by sorry
