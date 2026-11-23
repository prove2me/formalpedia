-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_comm_of_stable
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.comm_of_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:03.936573+00:00
-- url     : https://prove2.me/theorems/cc8a0c78-ee7e-4d9e-a65a-c54c36df0dc8
-- title:
--   Finitely Nonzero Linear: comm of stable
-- statement:
--   The Finitely Nonzero Linear construction uses the comm of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L386-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L386-L441

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.comm_of_stable {n : ℕ} {H : Matrix (Fin n) (Fin n) K} (hHh : Hᴴ = H) (hHu : IsUnit H)
    {𝒯 : Set (Matrix (Fin n) (Fin n) K)} (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T')
    {Z : Submodule K (Fin n → K)} (hZ : IsCommStable 𝒯 Z) {e : Matrix (Fin n) (Fin n) K}
    (heH : eᴴ * H = H * e) (h1 : ∀ x, e *ᵥ x ∈ Z) (h2 : ∀ z ∈ Z, e *ᵥ z = z)
    (B : Matrix (Fin n) (Fin n) K) (hB : ∀ T ∈ 𝒯, B * T = T * B) : e * B = B * e := by sorry
