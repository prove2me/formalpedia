-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_mul
-- name    : CompanionTheory.D.gk.RF.Lowers.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:34.551423+00:00
-- url     : https://prove2.me/theorems/212ad64e-ee69-4b53-bf0d-981e5e3173a6
-- title:
--   Lowers: mul
-- statement:
--   The Lowers construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L41-L42

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

theorem CompanionTheory.D.gk.RF.Lowers.mul (hW : Isot J W) {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    Lowers J W (A * B) := by sorry
