-- Prove2me | solution 1 for coveringNumber_Icc_zero_one_le_one_div
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:42:26.802615+00:00
-- url     : https://prove2.me/submissions/8b91f44b-3e44-48ff-ac21-9243e91cec00

import Definitions.Def_BrownianMotion_Continuity_CoveringNumber_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Covering and packing numbers

### References
- Vershynin, High-Dimensional Probability (section 4.2)
-/

@[expose] public section

open EMetric Set Metric
open scoped ENNReal NNReal

section PseudoEMetricSpace

variable {E : Type*} [PseudoEMetricSpace E] {r ε ε' : ℝ≥0} {A B C : Set E}

end PseudoEMetricSpace

theorem _root_.solution {ε : ℝ≥0} (hε : ε ≤ 1) :
    (coveringNumber ε (Set.Icc (0 : ℝ) 1) : ℝ≥0∞) ≤ 1 / ε := by
  classical
  rcases eq_or_ne ε 0 with h0 | h0
  · subst h0; simp
  set e : ℝ := (ε : ℝ) with he
  have hep : 0 < e := by rw [he]; exact_mod_cast pos_iff_ne_zero.2 h0
  have he1 : e ≤ 1 := by rw [he]; exact_mod_cast hε
  set n : ℕ := ⌈1 / (2 * e)⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hnge : 1 / (2 * e) ≤ n := Nat.le_ceil _
  set c : ℕ → ℝ := fun k => min ((2 * k + 1) * e) 1 with hc
  set C : Finset ℝ := (Finset.range n).image c with hC
  have hsub : (C : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro y hy
    simp only [hC, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hy
    obtain ⟨k, -, rfl⟩ := hy
    exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hcov : IsCover ε (Set.Icc (0 : ℝ) 1) (C : Set ℝ) := by
    rw [isCover_iff_subset_iUnion_closedBall]
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    set j : ℕ := ⌊x / (2 * e)⌋₊ with hj
    have hjle : (j : ℝ) ≤ x / (2 * e) := Nat.floor_le (by positivity)
    have hjlt : x / (2 * e) < j + 1 := Nat.lt_floor_add_one _
    have h2e : 0 < 2 * e := by positivity
    have hjx : 2 * j * e ≤ x := by
      have := (le_div_iff₀ h2e).1 hjle; linarith
    have hxj : x < 2 * (j + 1) * e := by
      have := (div_lt_iff₀ h2e).1 hjlt; linarith
    have hne : (n : ℝ) * (2 * e) ≥ 1 := by
      have := (div_le_iff₀ h2e).1 hnge; linarith
    have key : ∃ k < n, |x - c k| ≤ e := by
      by_cases hjn : j < n
      · refine ⟨j, hjn, ?_⟩
        simp only [hc]
        by_cases hm : (2 * (j : ℝ) + 1) * e ≤ 1
        · rw [min_eq_left hm, abs_le]; constructor <;> nlinarith
        · rw [min_eq_right (le_of_lt (not_le.1 hm)), abs_le]
          push_neg at hm
          constructor <;> nlinarith
      · push_neg at hjn
        refine ⟨n - 1, by omega, ?_⟩
        have hjn' : (n : ℝ) ≤ j := by exact_mod_cast hjn
        have hx : x = 1 := le_antisymm hx1 (by nlinarith)
        subst hx
        simp only [hc]
        rw [Nat.cast_sub hn1, Nat.cast_one]
        have hlow : 1 - e ≤ (2 * ((n : ℝ) - 1) + 1) * e := by nlinarith
        rw [abs_le]
        constructor
        · have := min_le_right ((2 * ((n : ℝ) - 1) + 1) * e) 1; linarith
        · have : 1 - e ≤ min ((2 * ((n : ℝ) - 1) + 1) * e) 1 := le_min hlow (by linarith)
          linarith
    obtain ⟨k, hk, hxk⟩ := key
    simp only [Set.mem_iUnion]
    refine ⟨c k, ?_, ?_⟩
    · simp only [hC, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
      exact ⟨k, hk, rfl⟩
    · rw [Metric.mem_closedBall, Real.dist_eq]; exact hxk
  have h1 : coveringNumber ε (Set.Icc (0 : ℝ) 1) ≤ (n : ℕ∞) := by
    refine (hcov.coveringNumber_le_encard hsub).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast (Finset.card_image_le.trans (by simp))
  have hnr : (n : ℝ) ≤ 1 / e := by
    by_cases hh : e ≤ 1 / 2
    · have := Nat.ceil_lt_add_one (show 0 ≤ 1 / (2 * e) by positivity)
      have h3 : 1 / (2 * e) + 1 ≤ 1 / e := by
        rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) hep]
        nlinarith
      rw [← hn] at this
      linarith
    · push_neg at hh
      have : n ≤ 1 := Nat.ceil_le.2 (by
        rw [div_le_iff₀ (by positivity)]; push_cast; linarith)
      have h4 : (1 : ℝ) ≤ 1 / e := by rw [le_div_iff₀ hep]; linarith
      have : (n : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
  calc (coveringNumber ε (Set.Icc (0 : ℝ) 1) : ℝ≥0∞) ≤ ((n : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.2 h1
    _ = ENNReal.ofReal (n : ℝ) := by simp
    _ ≤ ENNReal.ofReal (1 / e) := ENNReal.ofReal_le_ofReal hnr
    _ = 1 / ε := by
        rw [ENNReal.ofReal_div_of_pos hep, ENNReal.ofReal_one, he, ENNReal.ofReal_coe_nnreal]
