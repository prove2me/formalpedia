-- Prove2me | Theorems.Thm_FairSelling_sum_split_cover
-- name    : FairSelling.sum_split_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:22.680803+00:00
-- url     : https://prove2.me/theorems/84bcb527-0c6b-48d4-bef8-af1c5e18ddc7
-- title:
--   Fair Selling: sum split cover
-- statement:
--   If the goods are covered by the available set `R` together with the pairwise disjoint sets
--   `Gb b` of goods consumed by the past events, then any sum over a set `A` splits accordingly.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L42-L63
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L42-L63

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.sum_split_cover {f : G → ℝ} (A R : Finset G) (Gb : Fin n → Finset G)
    (hcov : (Finset.univ : Finset G) = R ∪ Finset.univ.biUnion Gb)
    (hRG : ∀ b, Disjoint R (Gb b)) (hGG : ∀ b b', b ≠ b' → Disjoint (Gb b) (Gb b')) :
    ∑ g ∈ A, f g = (∑ g ∈ A ∩ R, f g) + ∑ b, ∑ g ∈ A ∩ Gb b, f g := by sorry
