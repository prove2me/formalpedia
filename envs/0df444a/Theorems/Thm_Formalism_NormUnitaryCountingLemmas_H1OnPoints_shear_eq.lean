-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_shear_eq
-- name    : Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:37.527935+00:00
-- url     : https://prove2.me/theorems/2152c909-10a1-4a38-9034-484f95266e1f
-- title:
--   H1 On Points: shear eq
-- statement:
--   The H1 On Points construction uses the shear eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L54-L59

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe
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
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_eq {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν)
    (i j : Fin N) (hij : i < j) : shear R i j F = Polynomial.C F := by sorry
