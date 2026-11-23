-- Prove2me | Theorems.Thm_Formalism_L2_DIV_mem_dual_iff
-- name    : Formalism.L2.DIV.mem_dual_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:29.170818+00:00
-- url     : https://prove2.me/theorems/ba8280b9-6018-4f10-a3ad-1b5e2cbc2ef3
-- title:
--   DIV: mem dual iff
-- statement:
--   The DIV construction uses the mem dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1158-L1162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1158-L1162

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

theorem Formalism.L2.DIV.mem_dual_iff {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (h : (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K) (L : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by sorry
