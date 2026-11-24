-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_sum_biUnion_le
-- name    : FairSelling.PotTPS.QStage.sum_biUnion_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:02:22.172833+00:00
-- url     : https://prove2.me/theorems/5e4b65ce-6ce5-49f0-a8c6-f246e3a47fe2
-- title:
--   QStage: sum bi Union le
-- statement:
--   A sum over a union is at most the sum of the sums, for a non-negative summand.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L344-L353
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L344-L353

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
omit [Fintype G]

theorem FairSelling.PotTPS.QStage.sum_biUnion_le {ι : Type*} (T : Finset ι) (u : ι → Finset G) (f : G → ℝ)
    (hf : ∀ g, 0 ≤ f g) : ∑ g ∈ T.biUnion u, f g ≤ ∑ i ∈ T, ∑ g ∈ u i, f g := by sorry
