-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_skew_mul
-- name    : CompanionTheory.D.gk.RF.skew_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:40:26.88765+00:00
-- url     : https://prove2.me/theorems/3135edc4-6a07-4c72-9468-1702ce1bcd2e
-- title:
--   RF: skew mul
-- statement:
--   The RF construction uses the skew mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L62-L65

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

theorem CompanionTheory.D.gk.RF.skew_mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y)ᴴ * J = J * (Y * X) := by sorry
