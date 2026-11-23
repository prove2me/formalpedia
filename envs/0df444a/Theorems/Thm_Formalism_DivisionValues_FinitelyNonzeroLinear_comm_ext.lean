-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_comm_ext
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.comm_ext
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:56.618135+00:00
-- url     : https://prove2.me/theorems/0b2e3064-5b4d-4695-a1ef-97c967bb27ff
-- title:
--   Finitely Nonzero Linear: comm ext
-- statement:
--   The Finitely Nonzero Linear construction uses the comm ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L237-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L237-L249

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.comm_ext {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) {n : ℕ}
    {𝒯 : Set (Matrix (Fin n) (Fin n) K)} {e : Matrix (Fin n) (Fin n) K}
    (hec : ∀ B : Matrix (Fin n) (Fin n) K, (∀ T ∈ 𝒯, B * T = T * B) → e * B = B * e)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ T ∈ 𝒯, M * T.map j = T.map j * M) :
    e.map j * M = M * e.map j := by sorry
