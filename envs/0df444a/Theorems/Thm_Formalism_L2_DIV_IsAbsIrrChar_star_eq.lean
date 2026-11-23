-- Prove2me | Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_star_eq
-- name    : Formalism.L2.DIV.IsAbsIrrChar.star_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:42.519261+00:00
-- url     : https://prove2.me/theorems/0eaa43ac-61e0-4a4b-b75a-9e16e35729e4
-- title:
--   Is Abs Irr Char: star eq
-- statement:
--   The Is Abs Irr Char construction uses the star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L771-L774
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L771-L774

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.DIV.IsAbsIrrChar.star_eq {v0 : InfinitePlace K} (hv : IsConjAt v0) {χ : G → K} (h : IsAbsIrrChar χ)
    (t : G) : star (χ t) = χ t⁻¹ := by sorry
