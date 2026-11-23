-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ReductionFirst_hform_apply
-- name    : Formalism.DivisionValues.ReductionFirst.hform_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:00.395797+00:00
-- url     : https://prove2.me/theorems/76a9ddba-65e0-4b1f-8856-a68a085d1609
-- title:
--   Reduction First: hform apply
-- statement:
--   The Reduction First construction uses the hform apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L115-L120

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ReductionFirst.hform_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (y x : Fin n → K) :
    hform H y x = star y ⬝ᵥ (H *ᵥ x) := by sorry
