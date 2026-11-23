-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_fnl_mul_right
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.fnl_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:09.311702+00:00
-- url     : https://prove2.me/theorems/09ed3247-6b62-4773-aa3a-2b0bd2515d96
-- title:
--   Finitely Nonzero Linear: fnl mul right
-- statement:
--   The Finitely Nonzero Linear construction uses the fnl mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L112-L118

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
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.fnl_mul_right {l m n : ℕ} (ρ : Fnl j) (M : Matrix (Fin l) (Fin m) Ω)
    (A : Matrix (Fin m) (Fin n) K) : (M * A.map j).map ρ.toFun = M.map ρ.toFun * A := by sorry
