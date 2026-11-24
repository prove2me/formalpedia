-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_mem_dual_one
-- name    : Formalism.L2.DIV.CSD.mem_dual_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:19.394987+00:00
-- url     : https://prove2.me/theorems/7d003903-fad1-42a5-9510-e7b66f236a31
-- title:
--   CSD: mem dual one
-- statement:
--   The CSD construction uses the mem dual one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumBridge.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumBridge.lean#L38-L48

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

theorem Formalism.L2.DIV.CSD.mem_dual_one {K : Type} [Field K] [NumberField K] [StarRing K] (y : K) :
    y ∈ Formalism.HermitianLatticesTheory.dual (pairOne K) (1 : Submodule (𝓞 K) K) ↔ y ∈ (1 : Submodule (𝓞 K) K) := by sorry
