-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_hf_skew
-- name    : CompanionTheory.D.gk.RF.hf_skew
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:43.059181+00:00
-- url     : https://prove2.me/theorems/ef733f4a-01db-4d05-bbd3-5b1a0fdc763a
-- title:
--   RF: hf skew
-- statement:
--   The RF construction uses the hf skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L172-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L172-L175

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

theorem CompanionTheory.D.gk.RF.hf_skew {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) (x y : Fin n → K) :
    hf J (X *ᵥ x) y = -hf J x (X *ᵥ y) := by sorry
