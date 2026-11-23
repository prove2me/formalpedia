-- Prove2me | Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_map_inv
-- name    : Formalism.L2.DIV.IsAbsIrrChar.map_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:44.350829+00:00
-- url     : https://prove2.me/theorems/c374a32b-ea81-4cf6-9516-05525976dfa0
-- title:
--   Is Abs Irr Char: map inv
-- statement:
--   The Is Abs Irr Char construction uses the map inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L733-L763
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L733-L763

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.DIV.IsAbsIrrChar.map_inv {χ : G → K} (h : IsAbsIrrChar χ) (σ : K →+* ℂ) (t : G) :
    σ (χ t⁻¹) = starRingEnd ℂ (σ (χ t)) := by sorry
