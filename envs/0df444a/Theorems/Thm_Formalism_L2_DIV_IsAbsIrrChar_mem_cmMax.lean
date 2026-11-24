-- Prove2me | Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_mem_cmMax
-- name    : Formalism.L2.DIV.IsAbsIrrChar.mem_cmMax
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:38.935962+00:00
-- url     : https://prove2.me/theorems/16c9b501-6972-42aa-85e2-02eeeadd97cf
-- title:
--   Is Abs Irr Char: mem cm Max
-- statement:
--   The Is Abs Irr Char construction uses the mem cm Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L776-L780
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L776-L780

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

theorem Formalism.L2.DIV.IsAbsIrrChar.mem_cmMax {v0 : InfinitePlace K} (hv : IsConjAt v0) {χ : G → K} (h : IsAbsIrrChar χ)
    (t : G) : χ t ∈ cmMax K := by sorry
