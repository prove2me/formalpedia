-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_bagFilling_induction
-- name    : FairSelling.EqualProceedsBagFilling.bagFilling_induction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:44.761411+00:00
-- url     : https://prove2.me/theorems/8718b32f-aa92-42ea-a1b2-6dab35b104e3
-- title:
--   Equal Proceeds Bag Filling: bag Filling induction
-- statement:
--   **The bag-filling algorithm.**  If every agent `k` of the active set `T` has potential
--   `v'ₖ(R) + n·s ≥ |T| · tₖ`, then the remaining goods `R` can be distributed (some kept by the
--   agents, some sold with the proceeds shared equally) so that every active agent ends with
--   `tₖ/n`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L363-L465
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L363-L465

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

theorem FairSelling.EqualProceedsBagFilling.bagFilling_induction
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) (ht : ∀ i, 0 ≤ t i) (hn : 0 < n) :
    ∀ (T : Finset (Fin n)) (R : Finset G) (s : ℝ), 0 ≤ s →
      (∀ k ∈ T, (T.card : ℝ) * t k ≤ effSum (v k) p (t k) R + n * s) →
      ∃ (C : Fin n → Finset G) (D : Finset G),
        (∀ k, C k ⊆ R) ∧ D ⊆ R ∧
        (∀ j k, j ≠ k → Disjoint (C j) (C k)) ∧ (∀ k, Disjoint (C k) D) ∧
        ∀ k ∈ T, t k / n ≤ (∑ g ∈ C k, v k g) + s + priceSum p D / n := by sorry
