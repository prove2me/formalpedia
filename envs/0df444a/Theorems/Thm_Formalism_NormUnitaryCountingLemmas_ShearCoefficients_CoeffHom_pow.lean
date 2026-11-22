-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_pow
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:52.89131+00:00
-- url     : https://prove2.me/theorems/32e823dc-d60d-4899-af22-17bba281cf4e
-- title:
--   Coeff Hom: pow
-- statement:
--   The Coeff Hom construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L100-L104

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
variable {σ M : Type*} [AddCommMonoid M] {wt : σ → M}

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.pow {a : M} {P : Polynomial (MvPolynomial σ R)} (h : CoeffHom wt a P) (e : ℕ) :
    CoeffHom wt (e • a) (P ^ e) := by sorry
