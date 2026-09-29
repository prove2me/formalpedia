-- Prove2me | solution 1 for mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:01:44.549209+00:00
-- url     : https://prove2.me/submissions/c2b58726-3f91-440b-ac79-f7a879b99d17

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter Topology

universe u

set_option autoImplicit false
set_option warningAsError true

/-! A finite product of downward-closed local value bounds is itself
downward-closed at the exact product endpoint, even when each factor occurs
with an arbitrary natural multiplicity. -/

theorem solution
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (multiplicity : Fin n → ℕ)
    (tau : ℝ) (endpoint : Fin n → ℝ)
    (hendpoint : ∀ i, 0 < endpoint i)
    (hlocal : ∀ (i : Fin n) (V : ℝ),
      0 ≤ V → V < endpoint i →
      HasTauValueAtLeast (T i) tau V) :
    ∀ W : ℝ, 0 ≤ W →
      W < ∏ i, (endpoint i) ^ (multiplicity i) →
      HasTauValueAtLeast
        (TensorObj.kronFin n
          (fun i ↦ (T i).kronPow (multiplicity i))) tau W := by
  intro W hW hWendpoint
  let ratio : ℕ → ℝ := fun N ↦ (N : ℝ) / (N + 1)
  have hratio : Tendsto ratio atTop (nhds 1) := by
    simpa only [ratio] using
      (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hproduct : Tendsto
      (fun N : ℕ ↦
        ∏ i, (ratio N * endpoint i) ^ (multiplicity i))
      atTop
      (nhds (∏ i, (endpoint i) ^ (multiplicity i))) := by
    apply tendsto_finsetProd Finset.univ
    intro i hi
    simpa only [one_mul] using
      (hratio.mul tendsto_const_nhds).pow (multiplicity i)
  have heventually : ∀ᶠ N : ℕ in atTop,
      W < ∏ i, (ratio N * endpoint i) ^ (multiplicity i) :=
    hproduct.eventually (Ioi_mem_nhds hWendpoint)
  obtain ⟨N, hNpos, hNproduct⟩ :=
    ((eventually_gt_atTop 0).and heventually).exists
  have hratioPos : 0 < ratio N := by
    dsimp only [ratio]
    exact div_pos (by exact_mod_cast hNpos) (by positivity)
  have hratioLt : ratio N < 1 := by
    dsimp only [ratio]
    apply (div_lt_one (by positivity)).2
    norm_num
  let target : Fin n → ℝ := fun i ↦ ratio N * endpoint i
  let base : Fin n → ℝ := fun i ↦ (target i + endpoint i) / 2
  let productTarget : ℝ :=
    ∏ i, (target i) ^ (multiplicity i)
  have htarget : ∀ i, 0 ≤ target i := by
    intro i
    exact (mul_pos hratioPos (hendpoint i)).le
  have htargetEndpoint : ∀ i, target i < endpoint i := by
    intro i
    dsimp only [target]
    nlinarith [hendpoint i]
  have hbase : ∀ i, 0 < base i := by
    intro i
    have htpos : 0 < target i := by
      dsimp only [target]
      exact mul_pos hratioPos (hendpoint i)
    dsimp only [base]
    linarith [hendpoint i]
  have htargetBase : ∀ i, target i < base i := by
    intro i
    dsimp only [base]
    linarith [htargetEndpoint i]
  have hbaseEndpoint : ∀ i, base i < endpoint i := by
    intro i
    dsimp only [base]
    linarith [htargetEndpoint i]
  have hvalue : ∀ i,
      HasTauValueAtLeast (T i) tau (base i) := by
    intro i
    exact hlocal i (base i) (hbase i).le (hbaseEndpoint i)
  have hWproduct : W < productTarget := by
    simpa only [productTarget, target] using hNproduct
  obtain ⟨E, hE, hextract⟩ :=
    mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below
      T multiplicity tau base target hbase htarget htargetBase hvalue
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (TensorObj.kronFin n
      (fun i ↦ (T i).kronPow (multiplicity i)))
    tau W hW (fun r ↦ r * E)
  · simpa [nsmul_eq_mul, mul_comm] using
      ((tendsto_id : Tendsto (fun x : ℕ ↦ x) atTop atTop).nsmul_atTop hE)
  · exact tendsto_const_nhds
  · filter_upwards [] with r
    obtain ⟨q, A, B, C, hrestrict, hweight⟩ := hextract r
    refine ⟨q, A, B, C, hrestrict, ?_⟩
    have hpow : W ^ (r * E) ≤ productTarget ^ (r * E) :=
      (pow_le_pow_left₀ hW hWproduct.le) (r * E)
    simpa only [sub_zero, mul_one] using hpow.trans hweight
