-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_lowers_of_Z
-- name    : CompanionTheory.D.gk.RF.lowers_of_Z
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:42.053067+00:00
-- url     : https://prove2.me/theorems/4688c670-14b0-4848-a759-aec3cf5b11e6
-- title:
--   RF: lowers of Z
-- statement:
--   The RF construction uses the lowers of Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L37-L39

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

theorem CompanionTheory.D.gk.RF.lowers_of_Z (hW : Isot J W) {Z : Matrix (Fin n) (Fin n) K} (h1 : ∀ z ∈ perp J W, Z *ᵥ z = 0)
    (h2 : ∀ z, Z *ᵥ z ∈ W) : Lowers J W Z := by sorry
