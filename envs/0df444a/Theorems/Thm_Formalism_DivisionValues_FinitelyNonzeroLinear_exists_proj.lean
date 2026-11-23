-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_exists_proj
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.exists_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:44.794058+00:00
-- url     : https://prove2.me/theorems/b3281940-3b63-470a-9bcb-e118ff320369
-- title:
--   Finitely Nonzero Linear: exists proj
-- statement:
--   The Finitely Nonzero Linear construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L305-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L305-L367

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
open ConjugateWeightGram

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.exists_proj {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map v0.embedding).PosDef)
    (Z : Submodule K (Fin n → K)) :
    ∃ e : Matrix (Fin n) (Fin n) K, e * e = e ∧ eᴴ * H = H * e ∧ (∀ x, e *ᵥ x ∈ Z) ∧
      ∀ z ∈ Z, e *ᵥ z = z := by sorry
