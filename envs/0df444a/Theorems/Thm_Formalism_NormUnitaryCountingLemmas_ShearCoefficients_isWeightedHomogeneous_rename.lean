-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_isWeightedHomogeneous_rename
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.isWeightedHomogeneous_rename
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:45.691191+00:00
-- url     : https://prove2.me/theorems/2fbfea89-b28f-4526-a5b5-48882b802b8e
-- title:
--   Shear Coefficients: is Weighted Homogeneous rename
-- statement:
--   The Shear Coefficients construction uses the is Weighted Homogeneous rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L28-L38

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

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.isWeightedHomogeneous_rename {σ τ M : Type*} [AddCommMonoid M] {w : τ → M} {f : σ → τ}
    {m : M} {F : MvPolynomial σ R} (hF : F.IsWeightedHomogeneous (w ∘ f) m) :
    (rename f F).IsWeightedHomogeneous w m := by sorry
