-- Prove2me | Theorems.Thm_Formalism_L2_DIV_star_mem_cmMax
-- name    : Formalism.L2.DIV.star_mem_cmMax
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:17.175009+00:00
-- url     : https://prove2.me/theorems/ed9b7a8e-6fed-4ba3-8390-329427ad1b56
-- title:
--   DIV: star mem cm Max
-- statement:
--   The DIV construction uses the star mem cm Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L987-L992
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L987-L992

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

theorem Formalism.L2.DIV.star_mem_cmMax {K : Type} [Field K] [StarRing K] {a : K} (ha : a ∈ cmMax K) :
    star a ∈ cmMax K := by sorry
