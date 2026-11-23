-- Prove2me | Theorems.Thm_Formalism_DivisionValues_reduction_lemma_first
-- name    : Formalism.DivisionValues.reduction_lemma_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:08:12.908106+00:00
-- url     : https://prove2.me/theorems/bf25aebf-a449-490b-87ea-901b75526735
-- title:
--   Division Values: reduction lemma first
-- statement:
--   The Division Values construction uses the reduction lemma first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L131-L133

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

theorem Formalism.DivisionValues.reduction_lemma_first : LemmaRa := by sorry
