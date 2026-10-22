-- Prove2me | solution 1 for input_iterate_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:13:01.800947+00:00
-- url     : https://prove2.me/submissions/1ed8cc1c-3cd5-4564-a702-becb29ffdfb7

import Mathlib
import Definitions.Def_syracuseOrbitMin
set_option autoImplicit false

noncomputable section

attribute [instance] Classical.propDecidable

theorem solution :
    ∀ n₀ n : ℕ, Odd n →
      ((syracuseStep^[n₀] n : ℕ) : ℝ)
        ≤ (3 : ℝ) ^ n₀ * n / (2 : ℝ) ^ (Finset.sum Finset.univ (fun j : Fin n₀ => Nat.factorization (3 * (syracuseStep^[j.val] n) + 1) 2)) + (3 : ℝ) ^ n₀ := by
  intro n₀ n hn
  -- one-step facts
  have step : ∀ x : ℕ, Odd x → Odd (syracuseStep x) ∧ 1 ≤ Nat.factorization (3 * x + 1) 2 ∧
      (2 : ℝ) ^ (Nat.factorization (3 * x + 1) 2) * (syracuseStep x : ℝ) = 3 * (x : ℝ) + 1 := by
    intro x hx
    have hne : 3 * x + 1 ≠ 0 := by omega
    refine ⟨?_, ?_, ?_⟩
    · have hc := Nat.coprime_ordCompl Nat.prime_two hne
      unfold syracuseStep
      rcases Nat.even_or_odd (ordCompl[2] (3 * x + 1)) with he | ho
      · exfalso
        have h2 : 2 ∣ ordCompl[2] (3 * x + 1) := even_iff_two_dvd.mp he
        have := Nat.Coprime.eq_one_of_dvd hc h2
        omega
      · exact ho
    · apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two hne
      obtain ⟨k, hk⟩ := hx
      exact ⟨3 * k + 2, by omega⟩
    · have := Nat.ordProj_mul_ordCompl_eq_self (3 * x + 1) 2
      unfold syracuseStep
      have h := congrArg (fun m : ℕ => (m : ℝ)) this
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
      exact h
  have main : ∀ k : ℕ, Odd (syracuseStep^[k] n) ∧
      ((syracuseStep^[k] n : ℕ) : ℝ) ≤ (3 : ℝ) ^ k * n / (2 : ℝ) ^ (∑ j ∈ Finset.range k, Nat.factorization (3 * (syracuseStep^[j] n) + 1) 2) + (3 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp [hn]
    | succ k ih =>
      obtain ⟨hodd, hle⟩ := ih
      obtain ⟨hT, hv, hrel⟩ := step _ hodd
      rw [Function.iterate_succ_apply', Finset.sum_range_succ]
      refine ⟨hT, ?_⟩
      set x := syracuseStep^[k] n with hx
      set S := ∑ j ∈ Finset.range k, Nat.factorization (3 * (syracuseStep^[j] n) + 1) 2 with hS
      set v := Nat.factorization (3 * x + 1) 2 with hv'
      set U : ℝ := (3 : ℝ) ^ k * n / (2 : ℝ) ^ S with hU
      have h2v : (0 : ℝ) < 2 ^ v := by positivity
      have h2S : (0 : ℝ) < 2 ^ S := by positivity
      have h2 : (2 : ℝ) ≤ 2 ^ v := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v := pow_le_pow_right₀ (by norm_num) hv
      have hT' : (syracuseStep x : ℝ) = (3 * (x : ℝ) + 1) / 2 ^ v := by
        rw [eq_div_iff h2v.ne']; linarith
      have hk3 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
      rw [hT']
      rw [div_le_iff₀ h2v]
      have : (3 : ℝ) ^ (k + 1) * n / 2 ^ (S + v) = 3 * U / 2 ^ v := by
        rw [hU, pow_succ, pow_add]
        field_simp
      rw [this]
      have hU0 : 0 ≤ U := by positivity
      have hx' : (x : ℝ) ≤ U + 3 ^ k := hle
      have e1 : (3 * U / 2 ^ v + 3 ^ (k + 1)) * 2 ^ v = 3 * U + 3 ^ (k + 1) * 2 ^ v := by
        field_simp
      rw [e1]
      have : (3 : ℝ) ^ (k + 1) * 2 ≤ 3 ^ (k + 1) * 2 ^ v := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
      have h3 : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
      nlinarith
  have := (main n₀).2
  rw [Fin.sum_univ_eq_sum_range (fun j => Nat.factorization (3 * (syracuseStep^[j] n) + 1) 2) n₀]
  exact this
