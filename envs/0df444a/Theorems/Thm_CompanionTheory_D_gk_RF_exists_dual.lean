-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_exists_dual
-- name    : CompanionTheory.D.gk.RF.exists_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:30.684995+00:00
-- url     : https://prove2.me/theorems/942a13fb-f4ee-4d81-82a1-4b3cf7c9d4c4
-- title:
--   RF: exists dual
-- statement:
--   The RF construction uses the exists dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L206-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L206-L224

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

theorem CompanionTheory.D.gk.RF.exists_dual (hJ : Jᴴ = J) (hd : IsUnit J.det) {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → Fin n → K}
    (hv : LinearIndependent K v) : ∃ u : κ → Fin n → K, ∀ i j, hf J (u i) (v j) = if i = j then 1 else 0 := by sorry
