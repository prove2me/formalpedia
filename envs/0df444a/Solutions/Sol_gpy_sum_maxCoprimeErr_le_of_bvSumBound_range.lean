-- Prove2me | solution 1 for gpy_sum_maxCoprimeErr_le_of_bvSumBound_range
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T06:54:11.934994+00:00
-- url     : https://prove2.me/submissions/ad9f3ed1-092f-4fdf-be4c-f6858f911a56

/-
  Submission file for the Prove2Me problem `gpy_sum_maxCoprimeErr_le_of_bvSumBound_range`
  (publish3 batch, BDH partial, Oct 30, 2026).

  Self-contained: imports Mathlib only. Contains the verified bodies
  of the dependency chain used by the original proof, plus the restated
  theorem as top-level `theorem solution` in the problem's exact
  binder/statement form (statement taken from the problem payload, so
  the two are identical modulo the name). No sorry tactic, no axioms
  beyond the standard ones, no platform imports. The theorem is
  CONDITIONAL: its BV sum hypothesis is intact. Nothing here is
  claimed to discharge hDiv.
-/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false



noncomputable def primeCountAP (Y L r : ℕ) : ℕ :=
  ((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card

noncomputable def maxCoprimeErr (M : ℕ → ℕ → ℝ) (Y L : ℕ) : ℝ := by
  classical
  exact if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).max' h
    else 0

theorem coprimeResidues_nonempty {L : ℕ} (hLpos : 0 < L) :
    ((Finset.range L).filter (fun r => Nat.Coprime r L)).Nonempty := by
  by_cases hL1 : L = 1
  · subst hL1
    exact ⟨0, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by norm_num, by decide⟩⟩
  · exact ⟨1, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, Nat.coprime_one_left L⟩⟩

theorem maxCoprimeErr_nonneg (M : ℕ → ℕ → ℝ) (Y L : ℕ) :
    0 ≤ maxCoprimeErr M Y L := by
  classical
  unfold maxCoprimeErr
  by_cases himg : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).Nonempty
  · rw [dif_pos himg]
    obtain ⟨r₀, _, hr₀⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
    rw [← hr₀]
    exact abs_nonneg _
  · rw [dif_neg himg]

theorem sum_maxCoprimeErr_le_of_sum_bound (M : ℕ → ℕ → ℝ) (Y : ℕ) (S : Finset ℕ) (B : ℝ)
    (hB : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ S, abs ((primeCountAP Y q (v q) : ℝ) - M Y q) ≤ B) :
    ∑ L ∈ S, maxCoprimeErr M Y L ≤ B := by
  classical
  have hex : ∀ q : ℕ, ∃ r : ℕ, Nat.Coprime r q ∧
      maxCoprimeErr M Y q ≤ abs ((primeCountAP Y q r : ℝ) - M Y q) := by
    intro q
    by_cases hq0 : q = 0
    · subst hq0
      refine ⟨1, Nat.coprime_one_left 0, ?_⟩
      have hne0 : ¬ ((((Finset.range 0).filter (fun r => Nat.Coprime r 0)).image
          (fun r => abs ((primeCountAP Y 0 r : ℝ) - M Y 0)))).Nonempty := by
        rw [Finset.range_zero, Finset.filter_empty, Finset.image_empty]
        exact Finset.not_nonempty_empty
      unfold maxCoprimeErr
      rw [dif_neg hne0]
      exact abs_nonneg _
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have himg := (coprimeResidues_nonempty hqpos).image
        (fun r => abs ((primeCountAP Y q r : ℝ) - M Y q))
      obtain ⟨r₀, hr₀mem, hr₀eq⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
      refine ⟨r₀, (Finset.mem_filter.mp hr₀mem).2, ?_⟩
      unfold maxCoprimeErr
      rw [dif_pos himg, ← hr₀eq]
  choose v hvCop hvMax using hex
  calc ∑ L ∈ S, maxCoprimeErr M Y L
      ≤ ∑ L ∈ S, abs ((primeCountAP Y L (v L) : ℝ) - M Y L) :=
        Finset.sum_le_sum (fun L _ => hvMax L)
    _ ≤ B := hB v hvCop

theorem mem_bvRange_of_le_sq {Y R L : ℕ} {η : ℝ}
    (hL1 : 1 ≤ L) (hLR : L ≤ R ^ 2)
    (hlevel : (R : ℝ) ^ 2 < (Y : ℝ) ^ (1 / 2 - η)) :
    L ∈ (Finset.range ⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊).filter
      (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y : ℝ) ^ (1 / 2 - η)) := by
  have hle : (L : ℝ) ≤ (R : ℝ) ^ 2 := by
    have h : (L : ℝ) ≤ ((R ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hLR
    push_cast at h
    exact h
  have hlt : (L : ℝ) < (Y : ℝ) ^ (1 / 2 - η) := lt_of_le_of_lt hle hlevel
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hL1, hlt⟩
  have hceil : (L : ℝ) < ((⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊ : ℕ) : ℝ) :=
    lt_of_lt_of_le hlt (Nat.le_ceil _)
  exact_mod_cast hceil

theorem sum_maxCoprimeErr_le_of_bvSumBound_range (M : ℕ → ℕ → ℝ) (Y' R : ℕ)
    {η : ℝ} (B : ℝ)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M Y' L ≤ B := by
  classical
  have hmax0 : maxCoprimeErr M Y' 0 = 0 := by
    have hne0 : ¬ ((((Finset.range 0).filter (fun r => Nat.Coprime r 0)).image
        (fun r => abs ((primeCountAP Y' 0 r : ℝ) - M Y' 0)))).Nonempty := by
      rw [Finset.range_zero, Finset.filter_empty, Finset.image_empty]
      exact Finset.not_nonempty_empty
    unfold maxCoprimeErr
    rw [dif_neg hne0]
  have hsplit : (∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M Y' L)
      = ∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L : ℕ => 1 ≤ L),
        maxCoprimeErr M Y' L := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (R ^ 2 + 1))
      (fun L : ℕ => 1 ≤ L) (fun L => maxCoprimeErr M Y' L)]
    have hnot : (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L : ℕ => ¬ 1 ≤ L),
        maxCoprimeErr M Y' L) = 0 := by
      apply Finset.sum_eq_zero
      intro L hL
      rw [Finset.mem_filter] at hL
      have hL0 : L = 0 := by omega
      rw [hL0, hmax0]
    rw [hnot, add_zero]
  rw [hsplit]
  calc (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L : ℕ => 1 ≤ L),
          maxCoprimeErr M Y' L)
      ≤ ∑ L ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        maxCoprimeErr M Y' L := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro L hL
          rw [Finset.mem_filter, Finset.mem_range] at hL
          exact mem_bvRange_of_le_sq hL.2 (by omega) hlev
        · intro L _ _
          exact maxCoprimeErr_nonneg _ _ _
    _ ≤ B := sum_maxCoprimeErr_le_of_sum_bound M Y' _ _ hBV

theorem solution (M : ℕ → ℕ → ℝ) (Y' R : ℕ)
    {η : ℝ} (B : ℝ)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : (∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B)) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' h
    else 0) ≤ B := by
  exact sum_maxCoprimeErr_le_of_bvSumBound_range M Y' R B hlev hBV
