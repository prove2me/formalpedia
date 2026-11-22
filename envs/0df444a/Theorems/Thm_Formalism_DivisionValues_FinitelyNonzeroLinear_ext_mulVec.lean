-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_ext_mulVec
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.ext_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:44.882361+00:00
-- url     : https://prove2.me/theorems/b8fda2fb-0516-4075-9634-c521d450a93b
-- title:
--   Finitely Nonzero Linear: ext mul Vec
-- statement:
--   The Finitely Nonzero Linear construction uses the ext mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L231-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L231-L235

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.ext_mulVec {R : Type} [CommRing R] {m n : ℕ} {A A' : Matrix (Fin m) (Fin n) R}
    (h : ∀ x, A *ᵥ x = A' *ᵥ x) : A = A' := by sorry
