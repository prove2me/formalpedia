-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_triple
-- name    : CompanionTheory.D.gk.RF.Lowers.triple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:04.786319+00:00
-- url     : https://prove2.me/theorems/9ba16be5-0eaa-4497-bc08-853ed2a81a98
-- title:
--   Lowers: triple
-- statement:
--   The Lowers construction uses the triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L15-L17

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

theorem CompanionTheory.D.gk.RF.Lowers.triple {A B C : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B)
    (hC : Lowers J W C) : A * (B * C) = 0 := by sorry
