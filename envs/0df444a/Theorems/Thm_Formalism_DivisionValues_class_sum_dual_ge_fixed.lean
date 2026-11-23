-- Prove2me | Theorems.Thm_Formalism_DivisionValues_class_sum_dual_ge_fixed
-- name    : Formalism.DivisionValues.class_sum_dual_ge_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:15.427529+00:00
-- url     : https://prove2.me/theorems/87eb7cd8-c9f5-41c9-9805-c448b44f397a
-- title:
--   Division Values: class sum dual ge fixed
-- statement:
--   The Division Values construction uses the class sum dual ge fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L30-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ClassSumDualGeOfFamily.lean#L30-L48

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

theorem Formalism.DivisionValues.class_sum_dual_ge_fixed : ClassSumDualGeF := by sorry
