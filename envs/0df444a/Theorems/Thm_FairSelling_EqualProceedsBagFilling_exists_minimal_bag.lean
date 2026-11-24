-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_minimal_bag
-- name    : FairSelling.EqualProceedsBagFilling.exists_minimal_bag
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:36.208567+00:00
-- url     : https://prove2.me/theorems/4c2c4a6d-fa41-4c99-a204-d38bcb1bb7f8
-- title:
--   Equal Proceeds Bag Filling: exists minimal bag
-- statement:
--   Filling a bag: from any bundle that already satisfies some active agent one can pass to a
--   sub-bundle that satisfies some active agent but becomes insufficient for *every* active agent
--   as soon as one of its goods is removed.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L187-L201
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L187-L201

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)

theorem FairSelling.EqualProceedsBagFilling.exists_minimal_bag (T : Finset (Fin n)) (s : ℝ) : ∀ B : Finset G,
    (∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) B) →
    ∃ B' ⊆ B, (∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) B') ∧
      (∀ e ∈ B', ∀ k ∈ T, netSum n (v k) p (t k) (B' \ {e}) < t k / n - s) := by sorry
