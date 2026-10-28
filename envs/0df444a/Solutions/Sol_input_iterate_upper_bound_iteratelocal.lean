-- Prove2me | solution 1 for input_iterate_upper_bound_iteratelocal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:43:18.323526+00:00
-- url     : https://prove2.me/submissions/edad599d-16c6-4289-a3e2-fcf2a1412244

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section

attribute [instance] Classical.propDecidable

namespace IterateLocal

/-- The 2-adic valuation of `3n+1` (Tao 2022, section 1.2). -/
def syrVal_L213 (n : ℕ) : ℕ := Nat.factorization (3 * n + 1) 2

/-- The Syracuse valuation vector of length `n₀` (Tao 2022, (1.8)). -/
def valVec_L213 (n₀ : ℕ) (n : ℕ) : Fin n₀ → ℕ := fun j => syrVal_L213 (syracuseStep^[j.val] n)

/-- The valuation-vector sum (Tao 2022, (1.4)). -/
def valSum_L213 (n₀ n : ℕ) : ℕ := Finset.sum Finset.univ (fun j => valVec_L213 n₀ n j)

end IterateLocal

namespace S216SY
open IterateLocal

lemma step_eq (x : ℕ) : 2 ^ syrVal_L213 x * syracuseStep x = 3 * x + 1 := by
  unfold syrVal_L213 syracuseStep
  exact Nat.ordProj_mul_ordCompl_eq_self _ _

lemma step_odd (x : ℕ) : Odd (syracuseStep x) := by
  have h := Nat.coprime_ordCompl Nat.prime_two (by omega : 3 * x + 1 ≠ 0)
  unfold syracuseStep
  rcases Nat.even_or_odd (ordCompl[2] (3 * x + 1)) with he | ho
  · exfalso
    have : 2 ∣ ordCompl[2] (3 * x + 1) := even_iff_two_dvd.mp he
    have := Nat.Coprime.eq_one_of_dvd h this
    omega
  · exact ho

lemma val_pos {x : ℕ} (hx : Odd x) : 1 ≤ syrVal_L213 x := by
  unfold syrVal_L213
  have : 2 ∣ 3 * x + 1 := by
    obtain ⟨k, rfl⟩ := hx; exact ⟨3 * k + 2, by ring⟩
  exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (by omega)).mp this

lemma iter_odd (n : ℕ) (hn : Odd n) : ∀ k, Odd (syracuseStep^[k] n)
  | 0 => hn
  | k + 1 => by rw [Function.iterate_succ_apply']; exact step_odd _

lemma valSum_succ (k n : ℕ) : valSum_L213 (k + 1) n = valSum_L213 k n + syrVal_L213 (syracuseStep^[k] n) := by
  unfold valSum_L213 valVec_L213
  rw [Fin.sum_univ_castSucc]
  simp

end S216SY

open S216SY IterateLocal in
theorem solution :
    ∀ n₀ n : ℕ, Odd n →
      ((syracuseStep^[n₀] n : ℕ) : ℝ)
        ≤ (3 : ℝ) ^ n₀ * n / (2 : ℝ) ^ (IterateLocal.valSum_L213 n₀ n) + (3 : ℝ) ^ n₀ := by
  intro n₀ n hn
  induction n₀ with
  | zero => simp [valSum_L213]
  | succ k ih =>
    set x := syracuseStep^[k] n with hx
    set v := syrVal_L213 x
    have he : (2 : ℝ) ^ v * (syracuseStep x : ℝ) = 3 * x + 1 := by exact_mod_cast step_eq x
    have hv : 1 ≤ v := val_pos (iter_odd n hn k)
    have h2v : (0 : ℝ) < 2 ^ v := by positivity
    have hstep : (syracuseStep x : ℝ) = (3 * x + 1) / 2 ^ v := by
      rw [eq_div_iff h2v.ne', mul_comm]; exact he
    rw [Function.iterate_succ_apply', ← hx, hstep, valSum_succ]
    have h3 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ≤ 2 ^ v := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ v := pow_le_pow_right₀ (by norm_num) hv
    have hS : (0 : ℝ) < 2 ^ valSum_L213 k n := by positivity
    set A : ℝ := 3 * (3 ^ k * n / 2 ^ valSum_L213 k n) with hA
    have hg : (3 : ℝ) ^ (k + 1) * n / 2 ^ (valSum_L213 k n + v) = A / 2 ^ v := by
      rw [hA, pow_add, pow_succ]; field_simp; ring
    rw [hg]
    calc (3 * (x : ℝ) + 1) / 2 ^ v ≤ (A + 3 * 3 ^ k + 1) / 2 ^ v :=
          div_le_div_of_nonneg_right (by rw [hA]; linarith) h2v.le
      _ = A / 2 ^ v + (3 * 3 ^ k + 1) / 2 ^ v := by ring
      _ ≤ A / 2 ^ v + 3 ^ (k + 1) := by
          have : (3 * 3 ^ k + 1) / 2 ^ v ≤ (3 : ℝ) ^ (k + 1) := by
            rw [div_le_iff₀ h2v, pow_succ]; nlinarith
          linarith
