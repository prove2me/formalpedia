-- Prove2me | solution 1 for sidon_set_size_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:01:51.505296+00:00
-- url     : https://prove2.me/submissions/dfb9bd8c-19bd-45ba-b476-6a3f2d39a9ae

import Mathlib

set_option autoImplicit false

private theorem pair_count_bound (n : ℕ) (S : Finset (Fin n))
    (hS : ∀ a b c d : Fin n, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      a ≠ b → a.val + b.val = c.val + d.val →
      ({a, b} : Finset (Fin n)) = {c, d}) :
    S.card.choose 2 ≤ 2 * n := by
  classical
  let pairSum : Finset (Fin n) → ℕ := fun T => ∑ a ∈ T, a.val
  have hinj : Set.InjOn pairSum (S.powersetCard 2) := by
    intro T hT U hU he
    obtain ⟨hTS, hTc⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨hUS, hUc⟩ := Finset.mem_powersetCard.mp hU
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hTc
    obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hUc
    apply hS a b c d (hTS (by simp)) (hTS (by simp))
      (hUS (by simp)) (hUS (by simp)) hab
    simpa [pairSum, hab, hcd] using he
  have hsub : (S.powersetCard 2).image pairSum ⊆ Finset.range (2 * n) := by
    intro z hz
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, b, hab, rfl⟩ :=
      Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hT).2
    have ha := a.isLt
    have hb := b.isLt
    simp only [Finset.mem_range]
    simpa [pairSum, hab] using (show a.val + b.val < 2 * n by omega)
  calc
    S.card.choose 2 = (S.powersetCard 2).card := (Finset.card_powersetCard 2 S).symm
    _ = ((S.powersetCard 2).image pairSum).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (2 * n)).card := Finset.card_le_card hsub
    _ = 2 * n := Finset.card_range _

theorem sidon_three_sqrt_bound (n : ℕ) (S : Finset (Fin n))
    (hS : ∀ a b c d : Fin n, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      a ≠ b → a.val + b.val = c.val + d.val →
      ({a, b} : Finset (Fin n)) = {c, d}) :
    (S.card : ℝ) ≤ 3 * Real.sqrt n := by
  have hp : (S.card.choose 2 : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast pair_count_bound n S hS
  rw [Nat.cast_choose_two] at hp
  have hkNat : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hk : (S.card : ℝ) ≤ n := by exact_mod_cast hkNat
  have hs : (S.card : ℝ) ^ 2 ≤ 5 * n := by nlinarith
  have hr := Real.sq_sqrt (Nat.cast_nonneg n)
  have hn := Real.sqrt_nonneg (n : ℝ)
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hn)).mp
  nlinarith

theorem solution : ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (S : Finset (Fin n)),
      (∀ a b c d : Fin n, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
        a ≠ b → a.val + b.val = c.val + d.val →
        ({a, b} : Finset (Fin n)) = {c, d}) →
      (S.card : ℝ) ≤ C * Real.sqrt n * (1 + eps) := by
  intro eps heps
  refine ⟨3, by norm_num, ?_⟩
  intro n S hS
  have hb := sidon_three_sqrt_bound n S hS
  have he : 0 ≤ Real.sqrt (n : ℝ) * eps :=
    mul_nonneg (Real.sqrt_nonneg _) (le_of_lt heps)
  nlinarith

#print axioms solution
