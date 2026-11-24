-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_shear_rename_perm
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.shear_rename_perm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:53.071971+00:00
-- url     : https://prove2.me/theorems/0e233bdb-58b3-4f9e-9731-911f6abbff2a
-- title:
--   Shear Coefficients: shear rename perm
-- statement:
--   The Shear Coefficients construction uses the shear rename perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L40-L52

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
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
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.shear_rename_perm {N n : ℕ} (i j : Fin N) (σ : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin N × Fin n) R) :
    shear R i j (rename (fun p : Fin N × Fin n => (p.1, σ p.2)) F) =
      Polynomial.map (rename (R := R) (fun p : Fin N × Fin n => (p.1, σ p.2))).toRingHom
        (shear R i j F) := by sorry
