-- Prove2me | Theorems.Thm_Formalism_L2_NCov_mem_range_of_isRoot
-- name    : Formalism.L2.NCov.mem_range_of_isRoot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:37.482806+00:00
-- url     : https://prove2.me/theorems/8c5f2b73-fc9d-440b-9369-491b50d7fbd4
-- title:
--   NCov: mem range of is Root
-- statement:
--   The NCov construction uses the mem range of is Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverVal.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverVal.lean#L66-L74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Polynomial
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.L2.NCov.mem_range_of_isRoot (P : (FractionRing O)[X]) (hm : P.Monic)
    (hc : ∀ i, P.coeff i ∈ (algebraMap O (FractionRing O)).range) {μ : FractionRing O} (hμ : P.IsRoot μ) :
    μ ∈ (algebraMap O (FractionRing O)).range := by sorry
