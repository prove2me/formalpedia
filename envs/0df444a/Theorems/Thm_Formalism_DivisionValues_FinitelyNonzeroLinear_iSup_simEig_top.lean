-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_iSup_simEig_top
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.iSup_simEig_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:06.476724+00:00
-- url     : https://prove2.me/theorems/b07bcb76-b255-417d-a200-3c987726c541
-- title:
--   Finitely Nonzero Linear: i Sup sim Eig top
-- statement:
--   The Finitely Nonzero Linear construction uses the i Sup sim Eig top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L574-L636
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L574-L636

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
variable {K : Type} [Field K] {n : ℕ}

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.iSup_simEig_top (σ : K →+* ℂ) {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (hcomm : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T)
    (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ) :
    ⨆ χ : Matrix (Fin n) (Fin n) K → ℂ, simEig σ 𝒯 χ = ⊤ := by sorry
