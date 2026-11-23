-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_mul_perp
-- name    : CompanionTheory.D.gk.RF.Lowers.mul_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:01.999664+00:00
-- url     : https://prove2.me/theorems/ec9f9fb1-fd43-4484-8b80-2acec0e37bbd
-- title:
--   Lowers: mul perp
-- statement:
--   The Lowers construction uses the mul perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L32-L35

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}

theorem CompanionTheory.D.gk.RF.Lowers.mul_perp {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    (∀ z ∈ perp J W, (A * B) *ᵥ z = 0) ∧ ∀ z, (A * B) *ᵥ z ∈ W := by sorry
