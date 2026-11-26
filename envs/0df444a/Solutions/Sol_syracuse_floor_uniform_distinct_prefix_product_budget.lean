-- Prove2me | solution 1 for syracuse_floor_uniform_distinct_prefix_product_budget
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T11:14:59.235789+00:00
-- url     : https://prove2.me/submissions/41597bf8-40dc-4095-8d7d-d0d9c347d84d

import Mathlib
import Theorems.Thm_syracuse_uniform_logarithmic_tail_bound_ge_three

open Filter
open scoped Topology BigOperators

private theorem step_odd (x : ℕ) : Odd (syracuseStep x) := by
  have hn : ¬ 2 ∣ syracuseStep x := Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3*x+1 ≠ 0)
  exact Nat.odd_iff.mpr (by omega)

private theorem orbitMin_after_tail (n M N i : ℕ) (hi : N ≤ i)
    (hTail : ∀ j ≥ N, M < syracuseStep^[j] n) :
    M < syracuseOrbitMin (syracuseStep^[i] n) := by
  let y := syracuseStep^[i] n
  have hm : syracuseOrbitMin y ∈ Set.range (fun j : ℕ => syracuseStep^[j] y) :=
    Nat.sInf_mem (Set.range_nonempty _)
  obtain ⟨j, hj⟩ := hm
  change M < syracuseOrbitMin y
  rw [← hj]
  change M < syracuseStep^[j] (syracuseStep^[i] n)
  rw [← Function.iterate_add_apply]
  exact hTail _ (by omega)

private theorem product_le_exp_reciprocal_sum (n k : ℕ) (hn : 0 < n) :
    (2:ℝ)^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
      (syracuseStep^[k] n : ℝ) ≤
      (3:ℝ)^k*(n:ℝ)*Real.exp ((∑ i ∈ Finset.range k, 1/(syracuseStep^[i] n:ℝ))/3) := by
  let x (i : ℕ) := syracuseStep^[i] n
  let A (i : ℕ) := (Finset.range i).sum fun j => (3*x j+1).factorization 2
  let w (i : ℕ) : ℝ := 1/(x i:ℝ)
  let H (i : ℕ) := ∑ j ∈ Finset.range i, w j
  change (2:ℝ)^(A k)*(x k:ℝ) ≤ 3^k*(n:ℝ)*Real.exp (H k/3)
  induction k with
  | zero => simp [x,A,H]
  | succ k ih =>
    let a := (3*x k+1).factorization 2
    have hA : A (k+1) = A k+a := Finset.sum_range_succ _ _
    have hH : H (k+1) = H k+w k := Finset.sum_range_succ _ _
    have hrow : 2^a*x (k+1) = 3*x k+1 := by
      have hx : x (k+1) = syracuseStep (x k) := Function.iterate_succ_apply' _ _ _
      rw [hx]
      exact Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcast : (2:ℝ)^a*(x (k+1):ℝ) = 3*(x k:ℝ)+1 := by exact_mod_cast hrow
    have hx : (0:ℝ) < x k := by
      have h : 0 < x k := by
        cases k with
        | zero => exact hn
        | succ j =>
          change 0 < syracuseStep^[j+1] n
          rw [Function.iterate_succ_apply']
          exact Nat.ordCompl_pos 2 (by omega)
      exact_mod_cast h
    have hmul : 3+w k ≤ 3*Real.exp (w k/3) := by
      have h := Real.add_one_le_exp (w k/3)
      linarith
    rw [hA, pow_add, mul_assoc,hcast,hH,add_div,Real.exp_add,pow_succ]
    calc
      _ = ((2:ℝ)^(A k)*(x k:ℝ))*(3+w k) := by
        dsimp [w]
        field_simp [hx.ne']
      _ ≤ ((2:ℝ)^(A k)*(x k:ℝ))*(3*Real.exp (w k/3)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      _ ≤ (3^k*(n:ℝ)*Real.exp (H k/3))*(3*Real.exp (w k/3)) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by ring

theorem solution :
    ∃ D d : ℝ, 0 < D ∧ 0 < d ∧
      ∀ (n B k : ℕ), 3 ≤ B → 1 ≤ k → Odd n →
        Set.InjOn (fun i : ℕ => syracuseStep^[i] n) {i | i < k} →
        (∀ i : ℕ, B < syracuseStep^[i] n) →
        (2:ℝ)^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
          (syracuseStep^[k] n : ℝ) ≤
        Real.exp (1/3) * (n:ℝ) * (3:ℝ)^k *
          (((k:ℝ)+1)^(D/(Real.log (B:ℝ))^d)) := by
  classical
  obtain ⟨D,d,hD,hd,hLog⟩ := syracuse_uniform_logarithmic_tail_bound_ge_three
  refine ⟨D/3,d,by positivity,hd,?_⟩
  intro n B k hB hk hon hinj hf
  let x (i : ℕ) := syracuseStep^[i] n
  let w (i : ℕ) : ℝ := 1/(x i:ℝ)
  let Z := k+1
  let δ := D/(Real.log (B:ℝ))^d
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le B) (hf 0)
  have hZ : 2 ≤ Z := by omega
  have hZr : (0:ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hZl : 0 < Real.log (Z:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  let small := (Finset.range k).filter (fun i => x i ≤ Z)
  let large := (Finset.range k).filter (fun i => Z < x i)
  have hsum : (∑ i ∈ Finset.range k, w i) =
      (∑ i ∈ small, w i) + (∑ i ∈ large, w i) := by
    simpa only [small,large,not_le] using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.range k)
        (p := fun i => x i ≤ Z) (f := w)).symm
  have hlarge : (∑ i ∈ large, w i) ≤ 1 := by
    have hsub : large ⊆ Finset.range k := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    calc
      _ ≤ ∑ i ∈ large, (1:ℝ)/(Z:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hge : (Z:ℝ) ≤ (x i:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hi).2.le
        apply one_div_le_one_div_of_le hZr hge
      _ ≤ ∑ i ∈ Finset.range k, (1:ℝ)/(Z:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (k:ℝ)/(Z:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by apply (div_le_iff₀ hZr).mpr; simp [Z]
  let mass := weightedLogMassReal (fun v => 0 < v ∧ Odd v)
    (fun v => (B:ℝ) < (syracuseOrbitMin v:ℝ)) (fun v => 1/(v:ℝ)) (Z:ℝ)
  have hmass : mass ≤ δ := hLog B Z (by exact_mod_cast hB) (by exact_mod_cast hZ)
  let E := (Finset.range (Z+1)).filter
    (fun v => (0 < v ∧ Odd v) ∧ (B:ℝ) < (syracuseOrbitMin v:ℝ))
  have hEmass : (∑ v ∈ E, (1:ℝ)/(v:ℝ)) = mass*Real.log (Z:ℝ) := by
    unfold E mass weightedLogMassReal
    rw [Nat.floor_natCast, Finset.sum_filter]
    field_simp [hZl.ne']
  have himage : small.image x ⊆ E := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hiZ := (Finset.mem_filter.mp hi).2
    have himin : B < syracuseOrbitMin (x i) :=
      orbitMin_after_tail n B 0 i (Nat.zero_le _) (fun j _ => hf j)
    have hodd : Odd (x i) := by
      cases i with
      | zero => exact hon
      | succ i =>
        change Odd (syracuseStep^[i+1] n)
        rw [Function.iterate_succ_apply']
        exact step_odd _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hiZ),
      ⟨⟨lt_of_le_of_lt (Nat.zero_le _) (hf i),hodd⟩,by exact_mod_cast himin⟩⟩
  have hiSmall : Set.InjOn x (↑small : Set ℕ) := by
    intro i hi j hj hEq
    exact hinj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hEq
  have hsmall : (∑ i ∈ small, w i) ≤ δ * Real.log (Z:ℝ) := calc
    _ = ∑ v ∈ small.image x, (1:ℝ)/(v:ℝ) := by rw [Finset.sum_image hiSmall]
    _ ≤ ∑ v ∈ E, (1:ℝ)/(v:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
    _ = _ := hEmass
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass hZl.le
  let H := ∑ i ∈ Finset.range k, w i
  have he : H/3 ≤ 1/3+(δ/3)*Real.log (Z:ℝ) := by
    dsimp [H]
    rw [hsum]
    linarith only [hsmall,hlarge]
  calc
    _ ≤ (3:ℝ)^k*(n:ℝ)*Real.exp (H/3) := product_le_exp_reciprocal_sum n k hn
    _ ≤ (3:ℝ)^k*(n:ℝ)*Real.exp (1/3+(δ/3)*Real.log (Z:ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by
      rw [Real.exp_add, Real.rpow_def_of_pos (by positivity : (0:ℝ)<(k:ℝ)+1)]
      have hz : (Z:ℝ) = (k:ℝ)+1 := by simp [Z]
      rw [hz]
      dsimp [δ]
      have h : D/(Real.log (B:ℝ))^d/3 = (D/3)/(Real.log (B:ℝ))^d := by ring
      rw [h, mul_comm ((D/3)/(Real.log (B:ℝ))^d)]
      ring
