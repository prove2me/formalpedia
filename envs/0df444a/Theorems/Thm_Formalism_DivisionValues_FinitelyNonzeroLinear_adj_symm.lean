-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_adj_symm
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.adj_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:55.950332+00:00
-- url     : https://prove2.me/theorems/727ea7d7-8c1b-442f-9ce9-d5743200832e
-- title:
--   Finitely Nonzero Linear: adj symm
-- statement:
--   The Finitely Nonzero Linear construction uses the adj symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L523-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L523-L529

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.adj_symm (hH : Hc.PosDef) {N N' : Matrix (Fin n) (Fin n) ℂ} (hadj : Nᴴ * Hc = Hc * N') :
    N'ᴴ * Hc = Hc * N := by sorry
