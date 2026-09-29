-- Prove2me | solution 1 for mme_finite_kronFin_HasTauValueAtLeast_product_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:24:28.134987+00:00
-- url     : https://prove2.me/submissions/51a27eef-09b8-4901-a083-a6b5c73ce6bb

import Mathlib.Tactic
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_power_product_below
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (tau : ℝ)
    (base target : Fin n → ℝ)
    (hbase : ∀ i, 0 < base i)
    (htarget : ∀ i, 0 ≤ target i)
    (hstrict : ∀ i, target i < base i)
    (hvalue : ∀ i, HasTauValueAtLeast (T i) tau (base i)) :
    HasTauValueAtLeast
      (TensorObj.kronFin n T) tau (∏ i, target i) := by
  obtain ⟨E, hE, hextract⟩ :=
    mme_finite_HasTauValueAtLeast_common_power_product_below
      T tau base target hbase htarget hstrict hvalue
  have hprod : 0 ≤ ∏ i, target i := by
    exact Finset.prod_nonneg fun i _ ↦ htarget i
  let s : ℕ → ℕ := fun r ↦ r * E
  have hs : Tendsto s atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with r hr
    exact hr.trans (Nat.le_mul_of_pos_right r hE)
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (TensorObj.kronFin n T) tau (∏ i, target i) hprod
    s hs (fun _ ↦ (0 : ℝ)) tendsto_const_nhds
  filter_upwards [] with r
  obtain ⟨q, A, B, C, hrestrict, hweight⟩ := hextract r
  refine ⟨q, A, B, C, ?_, ?_⟩
  · simpa only [s] using hrestrict
  · simpa only [s, sub_zero, mul_one] using hweight
