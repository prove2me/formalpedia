-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_mul
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:11.523055+00:00
-- url     : https://prove2.me/theorems/5911a6ca-cce9-46a1-baaa-621374325306
-- title:
--   Coeff Hom: mul
-- statement:
--   The Coeff Hom construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L76-L80

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

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.mul {a b : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt a P)
    (hQ : CoeffHom wt b Q) : CoeffHom wt (a + b) (P * Q) := by sorry
