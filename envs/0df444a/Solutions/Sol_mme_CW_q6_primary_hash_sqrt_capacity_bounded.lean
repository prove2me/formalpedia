-- Prove2me | solution 1 for mme_CW_q6_primary_hash_sqrt_capacity_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:56:44.442349+00:00
-- url     : https://prove2.me/submissions/76abf4d6-af6c-4975-bb81-3006108cd80a

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_profile_capacity_sqrt_loss
import Theorems.Thm_mme_CW_q6_coupled_exact_floor_pruning
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true

private theorem combineOuterMiddleBoundsSqrtBounded
    {Z B X A H e : ℝ}
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hX : 0 < X)
    (hA0 : 0 ≤ A) (he : 0 ≤ e)
    (hA : Z * e ≤ A)
    (hH : B * e ≤ 4 * X ^ 2 * H) :
    ((Z ^ 3 * B ^ 2) / (16 * X ^ 4)) * e ^ 5 ≤
      A ^ 3 * H ^ 2 := by
  have hA3 : (Z * e) ^ 3 ≤ A ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hZ he) hA 3
  have hB2 : (B * e) ^ 2 ≤ (4 * X ^ 2 * H) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hB he) hH 2
  have hraw :
      Z ^ 3 * B ^ 2 * e ^ 5 ≤
        16 * X ^ 4 * (A ^ 3 * H ^ 2) := by
    calc
      Z ^ 3 * B ^ 2 * e ^ 5 = (Z * e) ^ 3 * (B * e) ^ 2 := by ring
      _ ≤ A ^ 3 * (4 * X ^ 2 * H) ^ 2 :=
        mul_le_mul hA3 hB2 (by positivity) (by positivity)
      _ = 16 * X ^ 4 * (A ^ 3 * H ^ 2) := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 16 * X ^ 4)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hraw

/-- The primary-hash capacity theorem with the fiber-size cap already
present in its uniform-stars input exposed in the conclusion. -/
theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let G : ℕ := N - L
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        ∃ A H : ℕ,
          ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            H ≤ 4 ^ N ∧
            raw ^ (2 * N) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
                ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  obtain ⟨C0, hC0, hprofile⟩ :=
    mme_CW_q6_primary_profile_capacity_sqrt_loss tau htau
  let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
  let LAt : ℕ → ℕ := fun N ↦ ⌊lambda * (N : ℝ)⌋₊
  let GAt : ℕ → ℕ := fun N ↦ N - LAt N
  obtain ⟨C1, hC1, hfamilies⟩ :=
    mme_CW_q6_primary_hash_uniform_stars_sqrt_loss LAt GAt
  have hpruning := mme_CW_q6_coupled_exact_floor_pruning tau htau
  refine ⟨C0 + 5 * C1, by positivity, ?_⟩
  filter_upwards [hfamilies, hpruning, eventually_ge_atTop 2] with
    N hfamilyN hprune hN
  dsimp only at hprune ⊢
  have hLAt : LAt N = ⌊lambda * (N : ℝ)⌋₊ := rfl
  have hGAt : GAt N = N - ⌊lambda * (N : ℝ)⌋₊ := by
    simp only [GAt, hLAt]
  rw [hLAt, hGAt] at hfamilyN
  have hconditions :
      0 < ⌊lambda * (N : ℝ)⌋₊ ∧
        ⌊lambda * (N : ℝ)⌋₊ +
            (N - ⌊lambda * (N : ℝ)⌋₊) = N ∧
        341 * ⌊lambda * (N : ℝ)⌋₊ <
          100 * (N - ⌊lambda * (N : ℝ)⌋₊) := by
    simpa only [lambda] using hprune
  obtain ⟨A, H, family, hHbound, hA, hB⟩ := hfamilyN hconditions
  refine ⟨A, H, family, hHbound, ?_⟩
  let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let X : ℕ := Nat.choose N G
  let B : ℕ := Nat.choose (2 * G) G
  let capacity : ℝ :=
    ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
  let sideTau : ℝ := ((((side * side * side : ℕ) : ℝ)) ^ tau)
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let e : ℝ := Real.exp (-C1 * x)
  change raw ^ (2 * N) * Real.exp (-(C0 + 5 * C1) * x) ≤
    (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * sideTau
  have hL : 0 < L := by simpa only [L] using hconditions.1
  have hLG : L + G = N := by
    simpa only [L, G] using hconditions.2.1
  have hG : 0 < G := by omega
  have hlambdaNonneg : 0 ≤ lambda * (N : ℝ) := by
    dsimp [lambda]
    positivity
  have hfloorLe : (L : ℝ) ≤ lambda * (N : ℝ) := by
    dsimp [L]
    exact Nat.floor_le hlambdaNonneg
  have hfloorLt : lambda * (N : ℝ) < (L : ℝ) + 1 := by
    dsimp [L]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (lambda * (N : ℝ))
  have hprofileN := hprofile N L G hN hL hG hLG
    (by simpa only [lambda] using hfloorLe)
    (by simpa only [lambda] using hfloorLt)
  dsimp only at hprofileN
  change raw ^ (2 * N) * Real.exp (-C0 * x) ≤
    capacity * sideTau at hprofileN
  change (Z : ℝ) * e ≤ (A : ℝ) at hA
  change (B : ℝ) * e ≤ 4 * (X : ℝ) ^ 2 * (H : ℝ) at hB
  have hXpos : 0 < (X : ℝ) := by
    dsimp [X]
    exact_mod_cast Nat.choose_pos (show G ≤ N by omega)
  have hcombine : capacity * e ^ 5 ≤ (A : ℝ) ^ 3 * (H : ℝ) ^ 2 := by
    exact combineOuterMiddleBoundsSqrtBounded
      (by positivity) (by positivity) hXpos (by positivity)
      (Real.exp_pos _).le hA hB
  have hexp :
      Real.exp (-(C0 + 5 * C1) * x) =
        Real.exp (-C0 * x) * e ^ 5 := by
    dsimp [e]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    raw ^ (2 * N) * Real.exp (-(C0 + 5 * C1) * x) =
        (raw ^ (2 * N) * Real.exp (-C0 * x)) * e ^ 5 := by
      rw [hexp]
      ring
    _ ≤ (capacity * sideTau) * e ^ 5 := by gcongr
    _ = (capacity * e ^ 5) * sideTau := by ring
    _ ≤ ((A : ℝ) ^ 3 * (H : ℝ) ^ 2) * sideTau := by gcongr
    _ = (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * sideTau := by
      norm_num
