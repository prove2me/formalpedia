-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_posDef_all
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.posDef_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:40.226087+00:00
-- url     : https://prove2.me/theorems/ffbcf23d-921d-49c8-9a9b-da80de72ad1a
-- title:
--   Finitely Nonzero Linear: pos Def all
-- statement:
--   The Finitely Nonzero Linear construction uses the pos Def all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L255-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L255-L267

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.posDef_all {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (σ : K →+* ℂ) :
    (H.map σ).PosDef := by sorry
