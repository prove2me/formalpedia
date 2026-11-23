-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_mem_perp_spanC
-- name    : CompanionTheory.D.gk.RF.mem_perp_spanC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:52.119472+00:00
-- url     : https://prove2.me/theorems/20521c9a-e5fd-4e71-a781-5ca80451e51e
-- title:
--   RF: mem perp span C
-- statement:
--   The RF construction uses the mem perp span C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L197-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L197-L204

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

theorem CompanionTheory.D.gk.RF.mem_perp_spanC {ι : Type} {w : ι → Fin n → K} {z : Fin n → K} (h : ∀ i, hf J (w i) z = 0) :
    z ∈ perp J (Submodule.span K (Set.range w)) := by sorry
