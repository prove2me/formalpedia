-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_skew_eq
-- name    : CompanionTheory.D.gk.RF.skew_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:10.616441+00:00
-- url     : https://prove2.me/theorems/4d1510a9-ce88-4f28-8b07-ac785e92ee8f
-- title:
--   RF: skew eq
-- statement:
--   The RF construction uses the skew eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L58-L59

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
variable [CharZero K]
omit [CharZero K]

theorem CompanionTheory.D.gk.RF.skew_eq {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) : Xᴴ * J = -(J * X) := by sorry
