-- Prove2me | solution 1 for mme_dwz_finite_candidate_family_common_prime_with_card_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:04:22.180405+00:00
-- url     : https://prove2.me/submissions/db6bcbb0-9dec-47ec-b15b-588c9409574e

import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Outer Block : Type}
    [Fintype Outer] [DecidableEq Outer] [Nonempty Outer]
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    (candidates : Outer → Block → Finset Outer)
    (d : ℕ) (R : ℝ)
    (hR : ∀ retained small, ((candidates retained small).card : ℝ) ≤ R) :
    ∃ Q p : ℕ,
      (∀ retained small, (candidates retained small).card ≤ Q) ∧
      Q ≤ Fintype.card Outer ∧
      (Q : ℝ) ≤ R ∧
      p.Prime ∧ Odd p ∧
      4 < p ∧
      8 * d ≤ p ∧
      (∀ retained small, 8 * (candidates retained small).card ≤ p) ∧
      max 4 (8 * max d Q) < p ∧
      p ≤ 2 * max 4 (8 * max d Q) ∧
      (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
  classical
  let counts : Finset ℕ := Finset.univ.image (fun x : Outer × Block ↦
    (candidates x.1 x.2).card)
  have hcounts : counts.Nonempty := by
    let x : Outer × Block := ⟨Classical.choice inferInstance,
      Classical.choice inferInstance⟩
    exact ⟨(candidates x.1 x.2).card,
      Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  let Q : ℕ := counts.max' hcounts
  have hQmem : Q ∈ counts := Finset.max'_mem counts hcounts
  have hQ : ∀ retained small, (candidates retained small).card ≤ Q := by
    intro retained small
    apply Finset.le_max' counts
    exact Finset.mem_image.mpr
      ⟨(retained, small), Finset.mem_univ (retained, small), rfl⟩
  have hQcard : Q ≤ Fintype.card Outer := by
    obtain ⟨x, _hx, hxeq⟩ := Finset.mem_image.mp hQmem
    rw [← hxeq]
    exact (candidates x.1 x.2).card_le_univ
  have hQR : (Q : ℝ) ≤ R := by
    obtain ⟨x, _hx, hxeq⟩ := Finset.mem_image.mp hQmem
    rw [← hxeq]
    exact hR x.1 x.2
  let M : ℕ := max d Q
  let M0 : ℕ := max 4 (8 * M)
  have hM0 : 2 ≤ M0 := le_trans (by decide) (le_max_left 4 (8 * M))
  have hlevel : 4 ≤ M0 := le_max_left _ _
  have hfirst : 8 * d ≤ M0 :=
    (Nat.mul_le_mul_left 8 (le_max_left d Q)).trans
      (le_max_right 4 (8 * M))
  have hcompatible : 8 * Q ≤ M0 :=
    (Nat.mul_le_mul_left 8 (le_max_right d Q)).trans
      (le_max_right 4 (8 * M))
  obtain ⟨p, hp, hpodd, h4p, hdp, hQp, hM0p, hpM0⟩ :=
    mme_dwz_claim6_8_exists_prime_modulus
      4 d Q M0 hM0 hlevel hfirst hcompatible
  have hfamily : ∀ retained small,
      8 * (candidates retained small).card ≤ p := by
    intro retained small
    exact (Nat.mul_le_mul_left 8 (hQ retained small)).trans hQp
  have hMR : (M : ℝ) ≤ max (d : ℝ) R := by
    simp only [M, Nat.cast_max]
    exact max_le_max (le_refl _) hQR
  have hpRate : (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
    by_cases hM : M = 0
    · have hp8 : p ≤ 8 := by
        dsimp only [M0] at hpM0
        simp only [hM, Nat.mul_zero, max_eq_left (by decide : 0 ≤ 4)] at hpM0
        omega
      exact (show (p : ℝ) ≤ 8 by exact_mod_cast hp8).trans (le_max_left _ _)
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
      have hp16 : p ≤ 16 * M := by
        dsimp only [M0] at hpM0
        have h48 : 4 ≤ 8 * M := by omega
        rw [max_eq_right h48] at hpM0
        omega
      have hp16R : (p : ℝ) ≤ 16 * (M : ℝ) := by exact_mod_cast hp16
      calc
        (p : ℝ) ≤ 16 * (M : ℝ) := hp16R
        _ ≤ 16 * max (d : ℝ) R := by gcongr
        _ ≤ max 8 (16 * max (d : ℝ) R) := le_max_right _ _
  refine ⟨Q, p, hQ, hQcard, hQR, hp, hpodd, h4p, hdp, hfamily,
    ?_, ?_, hpRate⟩
  · simpa only [M0, M] using hM0p
  · simpa only [M0, M] using hpM0
