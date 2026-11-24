-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_round_exists
-- name    : FairSelling.EqualProceedsBagFilling.round_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:49.158337+00:00
-- url     : https://prove2.me/theorems/fe383eb7-a2a3-4187-be62-2ec1828296ef
-- title:
--   Equal Proceeds Bag Filling: round exists
-- statement:
--   **One round of the bag-filling algorithm.**  If every still-active agent `k ∈ T` has
--   potential `v'ₖ(R) + n·s ≥ tₖ`, then some active agent `i` can be given a bundle `C` of kept
--   goods together with a set `D` of goods sold on her behalf so that
--
--   * `i` reaches her target: `tᵢ/n ≤ vᵢ(C) + s + p(D)/n`;
--   * every other active agent loses at most `tₖ` of potential:
--     `v'ₖ(C ∪ D) − p(D) ≤ tₖ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L210-L349
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L210-L349

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

theorem FairSelling.EqualProceedsBagFilling.round_exists
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) (ht : ∀ i, 0 ≤ t i) (hn : 0 < n)
    (R : Finset G) (s : ℝ) (hs : 0 ≤ s) (T : Finset (Fin n)) (hT : T.Nonempty)
    (hinv : ∀ k ∈ T, t k ≤ effSum (v k) p (t k) R + n * s) :
    ∃ i ∈ T, ∃ C D : Finset G, C ⊆ R ∧ D ⊆ R ∧ Disjoint C D ∧
      t i / n ≤ (∑ g ∈ C, v i g) + s + priceSum p D / n ∧
      (∀ k ∈ T, k ≠ i → effSum (v k) p (t k) (C ∪ D) - priceSum p D ≤ t k) := by sorry
