-- Prove2me | solution 1 for fixed_matrix_centered_sampling_log_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-25T06:36:07.195706+00:00
-- url     : https://prove2.me/submissions/d82e0c5e-faea-4fe6-9da0-86c36a562250

import Theorems.Thm_bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN
import Theorems.Thm_centered_sampling_log_moment_from_row_column_energy_2pN

open MatrixCompletion

/-- Decompose the fixed-matrix log-moment estimate (`fe0df420`) into the
strengthened `_2pN` controlled sampled row/column energy moment estimate and
the `_2pN` noncommutative-Khintchine conversion.

DESIGN NOTE (the gap and its resolution).  The bare energy supplier `4337294c`
(`bernoulli_sampled_row_column_energy_log_moment_bound`) returns an existential
`∃ q, 1 ≤ q ∧ q ≥ β log N ∧ energybound`; it does NOT re-export `q ≤ 2 β log N`
or `q ≤ 2 p N`.  But the `_2pN` Khintchine conversion below needs BOTH of those
on the supplied `q`.  The honest fix is the strengthened supplier
`bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN`, which
re-exports the two upper bounds — both established by `4337294c`'s exponent
window lemma `q_window_two_np` (`q ≤ β log N + 1 ≤ 2 β log N` and
`q ≤ 2 m/N ≤ 2 p N`).  That strengthened supplier is only valid for `2 ≤ N`
(when `N = 1` we have `log N = 0`, so `2 β log N = 0` and no `q ≥ 1` fits the
upper window).  The `N = 1` degenerate case (`n₁ = n₂ = 1`) is therefore handled
DIRECTLY here: the only feasible sample sizes are `m ∈ {0, 1}` and in both the
centered sampling fluctuation is the zero matrix (`m = 1 ⇒ p = 1 ⇒ P_Ω = I`;
`m = 0 ⇒ p = 0` and `0⁻¹ = 0`), so the left-hand side is `0` and the bound holds
with `q := 1` (the right-hand side carries the factor `√(β·1·log 1) = 0`). -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (C * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  classical
  rcases bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN with
    ⟨Cenergy, hCenergy, hEnergy⟩
  rcases centered_sampling_log_moment_from_row_column_energy_2pN Cenergy
      hCenergy with
    ⟨Cmoment, hCmoment, hKhintchine⟩
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
  by_cases hN2 : 2 ≤ max n₁ n₂
  · -- Non-degenerate regime: route through the strengthened supplier + `_2pN` Khintchine.
    exact hKhintchine β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
      (hEnergy β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hN2)
  · -- Degenerate `N = 1` regime: `max n₁ n₂ = 1`, so `n₁ = n₂ = 1` and `log N = 0`.
    push_neg at hN2
    -- `max n₁ n₂ < 2` and `0 < n₁, 0 < n₂` force `n₁ = n₂ = 1`.
    have hmax1 : max n₁ n₂ = 1 :=
      le_antisymm (Nat.lt_succ_iff.mp hN2) (le_trans hn₁ (le_max_left n₁ n₂))
    have hn₁1 : n₁ = 1 := le_antisymm (hmax1 ▸ le_max_left n₁ n₂) hn₁
    have hn₂1 : n₂ = 1 := le_antisymm (hmax1 ▸ le_max_right n₁ n₂) hn₂
    subst hn₁1; subst hn₂1
    refine ⟨1, le_refl 1, ?_, ?_⟩
    · -- q = 1 ≥ β log 1 = 0
      have hm1 : max 1 1 = 1 := rfl
      simp [hm1, Real.log_one]
    · -- LHS = 0: the surviving (positively weighted) fluctuation term is the zero matrix,
      -- so the whole Bernoulli expectation is 0; the RHS has the factor `√(β·1·log 1) = 0`.
      -- The right-hand side collapses to 0 first: `log (max 1 1) = log 1 = 0`,
      -- so `√(β·1·0/…) = 0` and the whole RHS is `(C·0·‖X‖)^1 = 0`.
      have hmaxcast : ((max (1 : ℕ) 1 : ℕ) : ℝ) = 1 := by norm_num
      rw [hmaxcast, Real.log_one, mul_zero, zero_div, Real.sqrt_zero,
        mul_zero, zero_mul, pow_one]
      -- Now show LHS ≤ 0 (the `pow_one` above already collapsed the inner power);
      -- combined with LHS ≥ 0 this forces LHS = 0.
      -- The universe `Finset (Fin 1 × Fin 1)` has exactly two elements: ∅ and {(0,0)}.
      -- Evaluate the expectation as a finite sum and discharge by `interval_cases m`.
      interval_cases m
      · -- m = 0 ⇒ p = 0.  weight(∅) = 1, weight of the full set = 0, and fluct(∅) = 0.
        unfold bernoulliExpectation bernoulliObservationWeight
        simp only [pow_one]
        apply Finset.sum_nonpos
        intro Omega _
        by_cases hΩ : Omega = (∅ : Finset (Fin 1 × Fin 1))
        · subst hΩ
          have : spectralNorm (centeredSamplingFluctuation (∅ : Finset (Fin 1 × Fin 1))
              ((0 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X) = 0 := by
            have : centeredSamplingFluctuation (∅ : Finset (Fin 1 × Fin 1))
                ((0 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X = 0 := by
              ext i j
              simp [centeredSamplingFluctuation, samplingProjection]
            rw [this]; unfold spectralNorm; simp
          simp only [Nat.cast_zero, Nat.cast_one] at this ⊢
          rw [this]; exact (mul_zero _).le
        · -- Ω ≠ ∅ ⇒ |Ω| ≥ 1 ⇒ weight = 0^|Ω|·… = 0.
          have hcard : 0 < Omega.card :=
            Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hΩ)
          have hz : ((0 : ℝ)) ^ Omega.card = 0 := zero_pow hcard.ne'
          simp only [Nat.cast_zero, zero_div, hz, zero_mul, mul_zero, le_refl]
      · -- m = 1 ⇒ p = 1.  weight(∅) = 0, weight(full) = 1, fluct(full) = 0.
        unfold bernoulliExpectation bernoulliObservationWeight
        simp only [pow_one]
        apply Finset.sum_nonpos
        intro Omega _
        by_cases hΩ : Omega = (Finset.univ : Finset (Fin 1 × Fin 1))
        · subst hΩ
          have hfz : centeredSamplingFluctuation (Finset.univ : Finset (Fin 1 × Fin 1))
              ((1 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X = 0 := by
            ext i j
            fin_cases i; fin_cases j
            simp [centeredSamplingFluctuation, samplingProjection]
          have : spectralNorm (centeredSamplingFluctuation
              (Finset.univ : Finset (Fin 1 × Fin 1))
              ((1 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X) = 0 := by
            rw [hfz]; unfold spectralNorm; simp
          simp only [Nat.cast_zero, Nat.cast_one] at this ⊢
          rw [this]; exact (mul_zero _).le
        · -- Ω ≠ univ ⇒ |Ωᶜ| ≥ 1 ⇒ card univ - |Ω| ≥ 1 ⇒ (1-1)^… = 0^… = 0.
          have hcardlt : Omega.card < Fintype.card (Fin 1 × Fin 1) := by
            rcases lt_or_eq_of_le (Finset.card_le_univ Omega) with h | h
            · simpa using h
            · exact absurd (Finset.card_eq_iff_eq_univ Omega |>.mp (by simpa using h)) hΩ
          have hpos : 0 < Fintype.card (Fin 1 × Fin 1) - Omega.card :=
            Nat.sub_pos_of_lt hcardlt
          have hz : ((0 : ℝ)) ^ (Fintype.card (Fin 1 × Fin 1) - Omega.card) = 0 :=
            zero_pow hpos.ne'
          have h11 : (1 : ℝ) / ((1 : ℝ) * (1 : ℝ)) = 1 := by norm_num
          simp only [Nat.cast_one, h11, sub_self, hz, mul_zero, zero_mul, le_refl]
