-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_hf_smul_leftC
-- name    : CompanionTheory.D.gk.RF.hf_smul_leftC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:50.356185+00:00
-- url     : https://prove2.me/theorems/2ff9db8f-0a13-4eed-b847-7d0b5d7aa0b6
-- title:
--   RF: hf smul left C
-- statement:
--   The RF construction uses the hf smul left C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L165-L166

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

theorem CompanionTheory.D.gk.RF.hf_smul_leftC (c : K) (x y : Fin n → K) : hf J (c • x) y = star c * hf J x y := by sorry
