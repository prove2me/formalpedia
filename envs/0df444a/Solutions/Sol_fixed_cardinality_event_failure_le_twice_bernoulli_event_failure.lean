-- Prove2me | solution 1 for fixed_cardinality_event_failure_le_twice_bernoulli_event_failure
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T03:46:08.323408+00:00
-- url     : https://prove2.me/submissions/ab1076ee-2e7a-48e0-aef1-f21cefa31c76

import Theorems.Thm_bernoulli_event_failure_probability_decomposes_by_cardinality
import Theorems.Thm_fixed_cardinality_event_probability_monotone_of_event_mono
import Theorems.Thm_binomial_lower_tail_at_integer_mean_ge_half
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
open MatrixCompletion
open scoped Classical BigOperators
open Finset

namespace SolAux2

variable {n₁ n₂ : ℕ}

/-- The fixed-cardinality probability is at most 1. -/
theorem prob_le_one (k : ℕ) (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    fixedCardinalityEventProb k Event ≤ 1 := by
  unfold fixedCardinalityEventProb
  simp only
  rcases Nat.eq_zero_or_pos
    ((Finset.powersetCard k (Finset.univ : Finset (Fin n₁ × Fin n₂))).card) with h0 | hpos
  · rw [h0]; simp
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- The fixed-cardinality probability is nonnegative. -/
theorem prob_nonneg (k : ℕ) (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ fixedCardinalityEventProb k Event := by
  unfold fixedCardinalityEventProb
  simp only
  positivity

end SolAux2

theorem solution
    {n₁ n₂ : ℕ} (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    1 - fixedCardinalityEventProb m Event ≤
      2 *
        (1 - bernoulliEventProb
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Event) := by
  intro hn1 hn2 hm hmono
  set M := n₁ * n₂ with hM
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hMpos : 0 < M := Nat.mul_pos hn1 hn2
  have hMR : ((n₁ : ℝ) * (n₂ : ℝ)) = (M : ℝ) := by
    rw [hM]; push_cast; ring
  -- p = m / M, with 0 ≤ p ≤ 1
  have hp0 : 0 ≤ p := by
    rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, hMR, div_le_one (by exact_mod_cast hMpos)]
    exact_mod_cast hm
  -- decomposition of failure probability
  have hdecomp := bernoulli_event_failure_probability_decomposes_by_cardinality
    (n₁ := n₁) (n₂ := n₂) p Event hp0 hp1
  -- abbreviations
  set f : ℕ → ℝ := fun k =>
    binomialCardinalityProb M k p * (1 - fixedCardinalityEventProb k Event) with hf
  -- nonnegativity of each term
  have hbinom_nonneg : ∀ k, 0 ≤ binomialCardinalityProb M k p := by
    intro k
    rw [binomialCardinalityProb]
    have : 0 ≤ 1 - p := by linarith
    positivity
  have hterm_nonneg : ∀ k, 0 ≤ f k := by
    intro k
    rw [hf]
    apply mul_nonneg (hbinom_nonneg k)
    have := SolAux2.prob_le_one k Event
    linarith
  -- 1 - bern = ∑_{k ∈ range(M+1)} f k
  have hbern_eq : 1 - bernoulliEventProb p Event
      = ∑ k ∈ Finset.range (M + 1), f k := by
    rw [hdecomp]
  -- restrict to range (m+1) ⊆ range (M+1)
  have hsubset : Finset.range (m + 1) ⊆ Finset.range (M + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (Nat.succ_le_succ hm)
  have hlow : ∑ k ∈ Finset.range (m + 1), f k
      ≤ ∑ k ∈ Finset.range (M + 1), f k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro k _ _; exact hterm_nonneg k
  -- on range(m+1): f k ≥ binom_k * (1 - prob_m)
  have hcmp : ∀ k ∈ Finset.range (m + 1),
      binomialCardinalityProb M k p * (1 - fixedCardinalityEventProb m Event) ≤ f k := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [hf]
    apply mul_le_mul_of_nonneg_left _ (hbinom_nonneg k)
    have hmonoP := fixed_cardinality_event_probability_monotone_of_event_mono
      (n₁ := n₁) (n₂ := n₂) Event hmono k m hk hm
    linarith
  have hstep : (1 - fixedCardinalityEventProb m Event)
        * (∑ k ∈ Finset.range (m + 1), binomialCardinalityProb M k p)
      ≤ ∑ k ∈ Finset.range (m + 1), f k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [mul_comm]
    exact hcmp k hk
  -- the lower tail = ∑_{k≤m} binom_k ≥ 1/2 at p = m/M
  have htail_eq : binomialLowerTailProb M m p
      = ∑ k ∈ Finset.range (m + 1), binomialCardinalityProb M k p := by
    rw [binomialLowerTailProb]
  have htail_half : (1 / 2 : ℝ)
      ≤ ∑ k ∈ Finset.range (m + 1), binomialCardinalityProb M k p := by
    rw [← htail_eq]
    have := binomial_lower_tail_at_integer_mean_ge_half M m hm
    -- the lemma uses p = m / M; rewrite
    have hpeq : p = (m : ℝ) / (M : ℝ) := by rw [hp, hMR]
    rw [hpeq]
    exact this
  -- 1 - prob_m ≥ 0
  have hprobm_le : fixedCardinalityEventProb m Event ≤ 1 := SolAux2.prob_le_one m Event
  have hfac_nonneg : 0 ≤ 1 - fixedCardinalityEventProb m Event := by linarith
  -- combine
  have hchain : (1 - fixedCardinalityEventProb m Event) * (1 / 2)
      ≤ 1 - bernoulliEventProb p Event := by
    calc (1 - fixedCardinalityEventProb m Event) * (1 / 2)
        ≤ (1 - fixedCardinalityEventProb m Event)
            * (∑ k ∈ Finset.range (m + 1), binomialCardinalityProb M k p) := by
          apply mul_le_mul_of_nonneg_left htail_half hfac_nonneg
      _ ≤ ∑ k ∈ Finset.range (m + 1), f k := hstep
      _ ≤ ∑ k ∈ Finset.range (M + 1), f k := hlow
      _ = 1 - bernoulliEventProb p Event := hbern_eq.symm
  linarith
