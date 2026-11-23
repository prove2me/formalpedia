-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_ker_pow_normal
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.ker_pow_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:08.961809+00:00
-- url     : https://prove2.me/theorems/2fabfd99-ec13-490f-8d6c-327810a6c521
-- title:
--   Finitely Nonzero Linear: ker pow normal
-- statement:
--   The Finitely Nonzero Linear construction uses the ker pow normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L540-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L540-L566

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.ker_pow_normal (hH : Hc.PosDef) {N N' : Matrix (Fin n) (Fin n) ℂ}
    (hadj : Nᴴ * Hc = Hc * N') (hc : N * N' = N' * N) (k : ℕ) (x : Fin n → ℂ)
    (h : (N ^ k) *ᵥ x = 0) : N *ᵥ x = 0 := by sorry
