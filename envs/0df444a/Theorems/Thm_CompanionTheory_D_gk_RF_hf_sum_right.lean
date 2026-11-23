-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_hf_sum_right
-- name    : CompanionTheory.D.gk.RF.hf_sum_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:44.549297+00:00
-- url     : https://prove2.me/theorems/9ddf1c0a-7e47-49f6-a788-dc9ad6424b20
-- title:
--   RF: hf sum right
-- statement:
--   The RF construction uses the hf sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L155-L157

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

theorem CompanionTheory.D.gk.RF.hf_sum_right {ι : Type} (s : Finset ι) (x : Fin n → K) (y : ι → Fin n → K) :
    hf J x (∑ i ∈ s, y i) = ∑ i ∈ s, hf J x (y i) := by sorry
