-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_rep_basis
-- name    : CompanionTheory.D.gk.RF.rep_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:40:12.782673+00:00
-- url     : https://prove2.me/theorems/2d84b912-2661-429b-b168-8ddb4d404187
-- title:
--   RF: rep basis
-- statement:
--   The RF construction uses the rep basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L226-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpotentSubgroupRepresentation.lean#L226-L274

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

theorem CompanionTheory.D.gk.RF.rep_basis [CharZero K] (hJ : Jᴴ = J) (hd : IsUnit J.det) (hW : Isot J W) {κ : Type} [Fintype κ]
    [DecidableEq κ] {v : κ → Fin n → K} (hv : LinearIndependent K v) (hs : Submodule.span K (Set.range v) = W)
    {X : Matrix (Fin n) (Fin n) K} (hX : InL J W X) :
    ∃ b : κ → Fin n → K, (∀ k, b k ∈ perp J W) ∧ ((∀ z, X *ᵥ z ∈ W) → ∀ k, b k ∈ W) ∧ X = ∑ k, xw J (v k) (b k) := by sorry
