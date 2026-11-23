-- Prove2me | Theorems.Thm_Formalism_DivisionValues_bounds_fourth_class_fixed
-- name    : Formalism.DivisionValues.bounds_fourth_class_fixed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:29.653005+00:00
-- url     : https://prove2.me/theorems/9131b2da-6cd2-4ae4-bc65-6dfe3deb9fc7
-- title:
--   Division Values: bounds fourth class fixed
-- statement:
--   The Division Values construction uses the bounds fourth class fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L150-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L150-L160

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
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
open exponent_index_lattice ValuationLatticeField
open ValuationLatticeField

theorem Formalism.DivisionValues.bounds_fourth_class_fixed : BoundsIVClassF := by sorry
