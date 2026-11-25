-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_map_conjTranspose_twist
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.map_conjTranspose_twist
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:00:40.23077+00:00
-- url     : https://prove2.me/theorems/e789f7cb-7421-5ba5-b2e8-b472583ec727
-- title:
--   Finitely Nonzero Linear: map conj Transpose twist
-- statement:
--   The Finitely Nonzero Linear construction uses the map conj Transpose twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L443-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L443-L447

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.map_conjTranspose_twist {m n : ℕ} (σ : K →+* ℂ) (A : Matrix (Fin m) (Fin n) K) :
    (Aᴴ).map σ = (A.map (twist σ))ᴴ := by sorry
