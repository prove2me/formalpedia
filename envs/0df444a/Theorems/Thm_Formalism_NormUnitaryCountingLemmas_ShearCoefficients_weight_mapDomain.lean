-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight_mapDomain
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.weight_mapDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:00.186362+00:00
-- url     : https://prove2.me/theorems/7a0c36e7-d87e-40aa-8215-257941e04b7a
-- title:
--   Shear Coefficients: weight map Domain
-- statement:
--   The Shear Coefficients construction uses the weight map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L21-L26

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

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (f : σ → τ)
    (d : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f d) = Finsupp.weight (w ∘ f) d := by sorry
