-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_adj_matrix
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.adj_matrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:32.520788+00:00
-- url     : https://prove2.me/theorems/b3efabe6-2a91-456e-b820-ec47d168a994
-- title:
--   Finitely Nonzero Linear: adj matrix
-- statement:
--   The Finitely Nonzero Linear construction uses the adj matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L375-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L375-L384

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.adj_matrix {n : ℕ} {H T T' : Matrix (Fin n) (Fin n) K}
    (h : ∀ x y : Fin n → K, hform H (T *ᵥ x) y = hform H x (T' *ᵥ y)) : Tᴴ * H = H * T' := by sorry
