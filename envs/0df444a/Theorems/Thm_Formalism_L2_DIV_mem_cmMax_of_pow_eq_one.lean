-- Prove2me | Theorems.Thm_Formalism_L2_DIV_mem_cmMax_of_pow_eq_one
-- name    : Formalism.L2.DIV.mem_cmMax_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:32.525163+00:00
-- url     : https://prove2.me/theorems/e51e316b-e610-46fe-a468-c09dee3cd091
-- title:
--   DIV: mem cm Max of pow eq one
-- statement:
--   The DIV construction uses the mem cm Max of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L484-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L484-L489

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.DIV.mem_cmMax_of_pow_eq_one {v0 : InfinitePlace K} (hv : IsConjAt v0) {u : K} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) : u ∈ cmMax K := by sorry
