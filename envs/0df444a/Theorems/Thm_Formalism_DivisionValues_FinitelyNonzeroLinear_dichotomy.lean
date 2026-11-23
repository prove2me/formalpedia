-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_dichotomy
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.dichotomy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:17.891885+00:00
-- url     : https://prove2.me/theorems/e3bcae15-15cd-472c-950a-e2cd2c8836fe
-- title:
--   Finitely Nonzero Linear: dichotomy
-- statement:
--   The Finitely Nonzero Linear construction uses the dichotomy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L671-L724
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L671-L724

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.dichotomy {K : Type} [Field K] (σ : K →+* ℂ) (hH : Hc.PosDef)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ)
    (E : Matrix (Fin n) (Fin n) ℂ) (hEE : E * E = E)
    (hEc : ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ T ∈ 𝒯, M * T.map σ = T.map σ * M) → E * M = M * E)
    (χ : Matrix (Fin n) (Fin n) K → ℂ) :
    (∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = y) ∨ (∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = 0) := by sorry
