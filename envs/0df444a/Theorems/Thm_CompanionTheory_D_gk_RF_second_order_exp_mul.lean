-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_second_order_exp_mul
-- name    : CompanionTheory.D.gk.RF.second_order_exp_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:55.427507+00:00
-- url     : https://prove2.me/theorems/d07464cb-c7dd-49a2-b02b-b78404f4b75c
-- title:
--   RF: second order exp mul
-- statement:
--   The RF construction uses the second order exp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L46-L52

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

theorem CompanionTheory.D.gk.RF.second_order_exp_mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Lowers J W X) (hY : Lowers J W Y) :
    ex2 X * ex2 Y = 1 + X + Y + (2 : K)⁻¹ • (X * X) + X * Y + (2 : K)⁻¹ • (Y * Y) := by sorry
