-- Prove2me | solution 1 for syracuse_valuation_prefix_residue
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T03:22:59.687262+00:00
-- url     : https://prove2.me/submissions/5e4f75a8-2d20-4d8d-81ea-ecaf1a6f3a50

/-
  Standalone deterministic residue forcing from a common Syracuse valuation
  prefix.  This is the generalized algebraic lemma; it makes no probability
  or exact-valuation claim.
-/

import Mathlib

private lemma int_chain_difference
    (k : ℕ) (a N₁ N₂ : ℕ → ℕ)
    (h₁ : ∀ i, i < k → 2 ^ a i * N₁ (i + 1) = 3 * N₁ i + 1)
    (h₂ : ∀ i, i < k → 2 ^ a i * N₂ (i + 1) = 3 * N₂ i + 1) :
    (2 : ℤ) ^ (∑ i ∈ Finset.range k, a i) *
        ((N₂ k : ℤ) - N₁ k) =
      (3 : ℤ) ^ k * ((N₂ 0 : ℤ) - N₁ 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h₁k := h₁ k (Nat.lt_succ_self k)
      have h₂k := h₂ k (Nat.lt_succ_self k)
      have hdiff :
          (2 : ℤ) ^ a k * ((N₂ (k + 1) : ℤ) - N₁ (k + 1)) =
            3 * ((N₂ k : ℤ) - N₁ k) := by
        have h₁kz :
            (2 : ℤ) ^ a k * (N₁ (k + 1) : ℤ) = 3 * (N₁ k : ℤ) + 1 := by
          exact_mod_cast h₁k
        have h₂kz :
            (2 : ℤ) ^ a k * (N₂ (k + 1) : ℤ) = 3 * (N₂ k : ℤ) + 1 := by
          exact_mod_cast h₂k
        calc
          (2 : ℤ) ^ a k * ((N₂ (k + 1) : ℤ) - N₁ (k + 1)) =
              ((2 : ℤ) ^ a k * (N₂ (k + 1) : ℤ)) -
                ((2 : ℤ) ^ a k * (N₁ (k + 1) : ℤ)) := by ring
          _ = (3 * (N₂ k : ℤ) + 1) - (3 * (N₁ k : ℤ) + 1) := by
            rw [h₂kz, h₁kz]
          _ = 3 * ((N₂ k : ℤ) - N₁ k) := by ring
      rw [Finset.sum_range_succ]
      calc
        (2 : ℤ) ^ (∑ i ∈ Finset.range k, a i + a k) *
              ((N₂ (k + 1) : ℤ) - N₁ (k + 1)) =
            (2 : ℤ) ^ (∑ i ∈ Finset.range k, a i) *
              ((2 : ℤ) ^ a k * ((N₂ (k + 1) : ℤ) - N₁ (k + 1))) := by
                rw [pow_add]
                ring
        _ = (3 : ℤ) *
              ((2 : ℤ) ^ (∑ i ∈ Finset.range k, a i) *
                ((N₂ k : ℤ) - N₁ k)) := by rw [hdiff]; ring
        _ = (3 : ℤ) ^ (k + 1) * ((N₂ 0 : ℤ) - N₁ 0) := by
          have h₁prefix : ∀ i, i < k → 2 ^ a i * N₁ (i + 1) = 3 * N₁ i + 1 :=
            fun i hi => h₁ i (lt_trans hi (Nat.lt_succ_self k))
          have h₂prefix : ∀ i, i < k → 2 ^ a i * N₂ (i + 1) = 3 * N₂ i + 1 :=
            fun i hi => h₂ i (lt_trans hi (Nat.lt_succ_self k))
          rw [ih h₁prefix h₂prefix]
          ring

/-- Deterministic residue forcing from a common finite valuation prefix. -/
theorem solution
    (k n' : ℕ) (a N₁ N₂ : ℕ → ℕ)
    (h₁ : ∀ i, i < k → 2 ^ a i * N₁ (i + 1) = 3 * N₁ i + 1)
    (h₂ : ∀ i, i < k → 2 ^ a i * N₂ (i + 1) = 3 * N₂ i + 1)
    (hS : (∑ i ∈ Finset.range k, a i) < n')
    (hfinal₁ : 2 ^ (n' - ∑ i ∈ Finset.range k, a i) ∣ 3 * N₁ k + 1)
    (hfinal₂ : 2 ^ (n' - ∑ i ∈ Finset.range k, a i) ∣ 3 * N₂ k + 1) :
    Nat.ModEq (2 ^ n') (N₁ 0) (N₂ 0) := by
  let S : ℕ := ∑ i ∈ Finset.range k, a i
  let R : ℕ := n' - S
  have hSR : S + R = n' := by
    dsimp [R]
    exact Nat.add_sub_of_le (Nat.le_of_lt hS)
  have hfinaldiff :
      (2 : ℤ) ^ R ∣ (3 : ℤ) * ((N₂ k : ℤ) - N₁ k) := by
    rcases hfinal₁ with ⟨q₁, hq₁⟩
    rcases hfinal₂ with ⟨q₂, hq₂⟩
    have hq₁z :
        (3 : ℤ) * (N₁ k : ℤ) + 1 = (2 : ℤ) ^ R * q₁ := by
      exact_mod_cast hq₁
    have hq₂z :
        (3 : ℤ) * (N₂ k : ℤ) + 1 = (2 : ℤ) ^ R * q₂ := by
      exact_mod_cast hq₂
    refine ⟨(q₂ : ℤ) - q₁, ?_⟩
    calc
      (3 : ℤ) * ((N₂ k : ℤ) - N₁ k) =
          (3 * (N₂ k : ℤ) + 1) - (3 * (N₁ k : ℤ) + 1) := by ring
      _ = (2 : ℤ) ^ R * ((q₂ : ℤ) - q₁) := by rw [hq₂z, hq₁z]; ring
  have hscaled :
      (2 : ℤ) ^ (S + R) ∣
        (2 : ℤ) ^ S * ((3 : ℤ) * ((N₂ k : ℤ) - N₁ k)) := by
    rcases hfinaldiff with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hq, pow_add]
    ring
  have hinitial :
      (2 : ℤ) ^ n' ∣
        (3 : ℤ) ^ (k + 1) * ((N₂ 0 : ℤ) - N₁ 0) := by
    have heq :
        (2 : ℤ) ^ S * ((3 : ℤ) * ((N₂ k : ℤ) - N₁ k)) =
          (3 : ℤ) ^ (k + 1) * ((N₂ 0 : ℤ) - N₁ 0) := by
      calc
        (2 : ℤ) ^ S * ((3 : ℤ) * ((N₂ k : ℤ) - N₁ k)) =
            3 * ((2 : ℤ) ^ S * ((N₂ k : ℤ) - N₁ k)) := by ring
        _ = 3 * ((3 : ℤ) ^ k * ((N₂ 0 : ℤ) - N₁ 0)) := by
          dsimp [S]
          rw [int_chain_difference k a N₁ N₂ h₁ h₂]
        _ = (3 : ℤ) ^ (k + 1) * ((N₂ 0 : ℤ) - N₁ 0) := by
          rw [pow_succ]
          ring
    rw [← hSR]
    rw [heq] at hscaled
    exact hscaled
  have hmul : Nat.ModEq (2 ^ n') (3 ^ (k + 1) * N₁ 0) (3 ^ (k + 1) * N₂ 0) := by
    apply Nat.modEq_iff_dvd.mpr
    simpa [Nat.cast_pow, Nat.cast_mul, mul_sub] using hinitial
  have hcop : Nat.Coprime (2 ^ n') (3 ^ (k + 1)) := by
    cases n' with
    | zero => simp
    | succ n' =>
        rw [Nat.coprime_pow_left_iff (Nat.zero_lt_succ _)]
        rw [Nat.coprime_pow_right_iff (Nat.zero_lt_succ _)]
        norm_num
  exact Nat.ModEq.cancel_left_of_coprime hcop hmul

#print axioms solution
