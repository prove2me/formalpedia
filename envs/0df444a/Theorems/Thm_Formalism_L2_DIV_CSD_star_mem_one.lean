-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_star_mem_one
-- name    : Formalism.L2.DIV.CSD.star_mem_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:07.231554+00:00
-- url     : https://prove2.me/theorems/85296553-4d53-4341-a321-94dfbc3fd324
-- title:
--   CSD: star mem one
-- statement:
--   The CSD construction uses the star mem one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumBridge.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumBridge.lean#L33-L36

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem Formalism.L2.DIV.CSD.star_mem_one {K : Type} [Field K] [NumberField K] [StarRing K] {z : K}
    (hz : z ∈ (1 : Submodule (𝓞 K) K)) : star z ∈ (1 : Submodule (𝓞 K) K) := by sorry
