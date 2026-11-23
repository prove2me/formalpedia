-- Prove2me | Theorems.Thm_Formalism_L2_DIV_map_injective_of_injective
-- name    : Formalism.L2.DIV.map_injective_of_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:39.642908+00:00
-- url     : https://prove2.me/theorems/15db7f46-c790-4ac3-8738-6028b7e766ba
-- title:
--   DIV: map injective of injective
-- statement:
--   The DIV construction uses the map injective of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1014-L1034
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1014-L1034

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

theorem Formalism.L2.DIV.map_injective_of_injective {K : Type} [Field K] {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective E.mulVec) (σ : K →+* ℂ) : Function.Injective (E.map σ).mulVec := by sorry
