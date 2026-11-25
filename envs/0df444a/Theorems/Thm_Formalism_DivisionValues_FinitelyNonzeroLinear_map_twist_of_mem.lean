-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_map_twist_of_mem
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.map_twist_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:50.521773+00:00
-- url     : https://prove2.me/theorems/cae49b2d-594f-46de-82e4-8109e0e37b84
-- title:
--   Finitely Nonzero Linear: map twist of mem
-- statement:
--   The Finitely Nonzero Linear construction uses the map twist of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L449-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L449-L453

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_HN_twist

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.map_twist_of_mem {K0 : Subfield K} (hK0 : IsCMSub K0) (σ : K →+* ℂ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : ∀ i k, A i k ∈ K0) : A.map (twist σ) = A.map σ := by sorry
