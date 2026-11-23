-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_form_adj
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.form_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:29.133606+00:00
-- url     : https://prove2.me/theorems/c87c6cb6-4456-4992-8839-58ce2c9bc102
-- title:
--   Finitely Nonzero Linear: form adj
-- statement:
--   The Finitely Nonzero Linear construction uses the form adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L648-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L648-L650

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.form_adj {A A' : Matrix (Fin n) (Fin n) ℂ} (h : Aᴴ * Hc = Hc * A') (u v : Fin n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ Hc *ᵥ v = star u ⬝ᵥ Hc *ᵥ (A' *ᵥ v) := by sorry
