-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_skew_of_hf
-- name    : CompanionTheory.D.gk.RF.skew_of_hf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:16.942885+00:00
-- url     : https://prove2.me/theorems/b1f74ed3-6b6a-4ac9-b6f6-d1ceb5b2daa7
-- title:
--   RF: skew of hf
-- statement:
--   The RF construction uses the skew of hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L177-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L177-L186

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

theorem CompanionTheory.D.gk.RF.skew_of_hf {X : Matrix (Fin n) (Fin n) K} (h : ∀ x y, hf J (X *ᵥ x) y = -hf J x (X *ᵥ y)) :
    Xᴴ * J + J * X = 0 := by sorry
