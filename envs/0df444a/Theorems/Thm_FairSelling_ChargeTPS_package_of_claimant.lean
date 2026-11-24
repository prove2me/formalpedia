-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_package_of_claimant
-- name    : FairSelling.ChargeTPS.package_of_claimant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:08.995939+00:00
-- url     : https://prove2.me/theorems/d022d777-1af2-49ce-a5db-1d3e6fe64fdd
-- title:
--   Charge TPS: package of claimant
-- statement:
--   **The owner-keeps post-processing.**  Given an admissible package `(S, S₀)` and an agent `k`
--   that claims it, move every good that `k` values below its price from the kept part to the sold
--   part.  The result is a package with the same footprint and the same cost, still claimed by `k`,
--   which `k` is willing to keep, and which is safe for everybody.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L138-L229
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L138-L229

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)
omit [Fintype G]

theorem FairSelling.ChargeTPS.package_of_claimant (hp : ∀ g, 0 ≤ p g) {S S₀ : Finset G} (hdisj : Disjoint S S₀)
    (hadm : CfgTPS.Adm v p req k0 D S S₀) (k : Fin n)
    (hclaim : req k ≤ vbarSum (v k) p S + CfgTPS.Qc v p req k0 S) :
    ∃ (S' S₀' : Finset G) (q : ℝ),
      S' ⊆ S ∧ S₀ ⊆ S₀' ∧ S' ∪ S₀' = S ∪ S₀ ∧ Disjoint S' S₀' ∧
      0 ≤ q ∧ q ≤ D + ∑ g ∈ S₀', p g ∧
      req k ≤ vbarSum (v k) p S' + q ∧ (∀ g ∈ S', p g ≤ v k g) ∧
      (∀ m, (vbarSum (v m) p S' + q ≤ req m) ∨
        (q = 0 ∧ ∀ g ∈ S', vbarSum (v m) p (S' \ {g}) + p g ≤ req m)) ∧
      (∀ (t : ℝ) (u : G → ℝ),
        truncBundle u p t S' + q + ∑ g ∈ S₀', saleLoss u p t g
          = truncBundle u p t S + CfgTPS.Qc v p req k0 S + ∑ g ∈ S₀, saleLoss u p t g) := by sorry
