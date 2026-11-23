-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_mat_extC
-- name    : CompanionTheory.D.gk.RF.mat_extC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:45.853356+00:00
-- url     : https://prove2.me/theorems/31880178-2986-4ba9-af0d-d3ea1ea88170
-- title:
--   RF: mat ext C
-- statement:
--   The RF construction uses the mat ext C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L12-L13

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
omit [StarRing K]

theorem CompanionTheory.D.gk.RF.mat_extC {A B : Matrix (Fin n) (Fin n) K} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B := by sorry
