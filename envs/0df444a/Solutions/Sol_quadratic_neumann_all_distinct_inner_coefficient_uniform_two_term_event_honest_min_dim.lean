-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_coefficient_uniform_two_term_event_honest_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:58:39.444232+00:00
-- url     : https://prove2.me/submissions/29baa99b-0ec6-4c23-a897-a51ba58f23ff

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-!
# Honest-scale uniform inner two-term event (node 1′)

Uniform sup-norm event for the all-distinct inner coefficient `G_{ω₃}(w1,w2)`
at the **honest** two-term Bernstein scale — i.e. carrying the `√(density)`
factor `√((β+4)logN/p)` explicitly, WITHOUT collapsing it into a `λ`-scale.

For every `Ω₃` on the event, and for every pair `(w1,w2)`,

  `|G_{ω₃}(w1,w2)| ≤ Cinner · twoTerm`, with product-Bernoulli probability
  `≥ 1 - cinner·N^{-β}`, where

  `twoTerm = √((β+4)logN/p) · (μ₁·√(R/(n₁n₂))·√(μ₀R/min))
           + ((β+4)logN/p)   · (μ₁·√(R/(n₁n₂))·(μ₀R/min))`.

The inner coefficient is a scalar function of TWO free coordinates `(w1,w2)`,
so the finite union is over `(n₁n₂)² ≤ N⁴` coordinates and is paid for by the
`β → β+4` two-power-times-two shift.  This is the sound analogue of the
`λ`-collapsed node
`quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_shifted`:
the ONLY change is that the two-term scale is kept intact — the `√(density)`
factor is not absorbed.

Source: Candès–Recht 2008, §6.3, PDF pp. 32--33, equation (6.23), and Lemma 6.6
equations (6.15)--(6.17).
-/

theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cinner cinner : ℝ, 0 < Cinner ∧ 0 < cinner ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner *
                  (Real.sqrt
                      (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  refine ⟨Cbern * max Cfro Centry, cbern, by positivity, hcbern, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hRep hEntry hFrob
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set Cmax : ℝ := max Cfro Centry with hCmax
  have hCmax_pos : 0 < Cmax := lt_max_of_lt_left hCfro
  have hβ4 : 2 < β + 4 := by linarith
  -- raw two-term scale (with Cfro/Centry from the base bounds) at exponent (β+4)
  set frobScaleRaw : ℝ :=
    Cfro * μ₁ *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) with hfrobScaleRaw
  set entryScaleRaw : ℝ :=
    Centry * μ₁ *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) with hentryScaleRaw
  set frobScaleTight : ℝ :=
    μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
      Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) with hfrobScaleTight
  set entryScaleTight : ℝ :=
    μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) with hentryScaleTight
  set rawTwoTerm : ℝ :=
    Real.sqrt (((β + 4) * Real.log N) / p) * frobScaleRaw +
      (((β + 4) * Real.log N) / p) * entryScaleRaw with hrawTwoTerm
  set targetTwoTerm : ℝ :=
    Real.sqrt (((β + 4) * Real.log N) / p) * frobScaleTight +
      (((β + 4) * Real.log N) / p) * entryScaleTight with htargetTwoTerm
  have hμ₀nn : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁nn : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  have hfrobScaleTight_nonneg : 0 ≤ frobScaleTight := by rw [hfrobScaleTight]; positivity
  have hentryScaleTight_nonneg : 0 ≤ entryScaleTight := by rw [hentryScaleTight]; positivity
  -- per-pair raw Bernstein tail at exponent (β+4)
  have hPair :
      ∀ w1 w2 : Fin n₁ × Fin n₂,
        bernoulliEventProb p
            (fun Omega3 =>
              |quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2| ≤
                Cbern * rawTwoTerm) ≥
          1 - cbern * Real.rpow N (-(β + 4)) := by
    intro w1 w2
    have hRep' :
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
          (fun Omega => quadraticAllDistinctInnerCoefficient Omega S p w1 w2) Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega p
                (quadraticAllDistinctInnerBaseMatrix S w1 w2)) := by
      intro Omega; simpa [hp] using hRep Omega w1 w2
    have hRaw :=
      hBernstein (β + 4) hβ4 n₁ n₂ m hn₁ hn₂ hm
        (fun Omega => quadraticAllDistinctInnerCoefficient Omega S p w1 w2)
        (quadraticAllDistinctInnerBaseMatrix S w1 w2)
        entryScaleRaw frobScaleRaw hRep' (hEntry w1 w2) (hFrob w1 w2)
    simpa [hp, hN, hrawTwoTerm, mul_assoc] using hRaw
  -- pair union bound (cardinality factor (n₁n₂)² ≤ N⁴)
  have hUnion :=
    bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
      Cbern cbern hCbern hcbern
      p rawTwoTerm (Real.rpow N (-(β + 4)))
      hp_nonneg hp_le_one n₁ n₂
      (fun w1 w2 Omega3 => quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2)
      hPair
  have hCardFail :
      ((Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * cbern) *
          Real.rpow N (-(β + 4)) ≤
        cbern * Real.rpow N (-β) := by
    have hN_pos_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_ge_one : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN_pos_nat
    have hN_pos : 0 < N := by rw [hN]; exact_mod_cast hN_pos_nat
    have hcard_eq :
        (Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) =
          ((n₁ : ℝ) * (n₂ : ℝ)) ^ 2 := by
      simp [Fintype.card_prod, Fintype.card_fin]; ring
    have hprod_le_N2 : (n₁ : ℝ) * (n₂ : ℝ) ≤ N ^ 2 := by
      have h1 : (n₁ : ℝ) ≤ N := by rw [hN]; exact_mod_cast Nat.le_max_left n₁ n₂
      have h2 : (n₂ : ℝ) ≤ N := by rw [hN]; exact_mod_cast Nat.le_max_right n₁ n₂
      nlinarith [Nat.cast_nonneg (α := ℝ) n₁, Nat.cast_nonneg (α := ℝ) n₂,
        le_trans zero_le_one hN_ge_one]
    have hcard_le_N4 :
        (Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) ≤ N ^ 4 := by
      rw [hcard_eq]
      calc ((n₁ : ℝ) * (n₂ : ℝ)) ^ 2
          ≤ (N ^ 2) ^ 2 := by apply pow_le_pow_left₀ (by positivity) hprod_le_N2
        _ = N ^ 4 := by ring
    have hN4_rpow : N ^ 4 = Real.rpow N 4 := by
      have := Real.rpow_natCast N 4; simpa using this.symm
    have hrpow_combine :
        Real.rpow N 4 * Real.rpow N (-(β + 4)) = Real.rpow N (-β) := by
      rw [show Real.rpow N 4 = N ^ (4 : ℝ) from rfl,
        show Real.rpow N (-(β + 4)) = N ^ (-(β + 4) : ℝ) from rfl,
        show Real.rpow N (-β) = N ^ (-β : ℝ) from rfl, ← Real.rpow_add hN_pos]
      congr 1; ring
    have hrpow_pos : 0 < Real.rpow N (-(β + 4)) := Real.rpow_pos_of_pos hN_pos _
    have hcbern_nonneg : 0 ≤ cbern := le_of_lt hcbern
    calc ((Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * cbern) *
            Real.rpow N (-(β + 4))
        ≤ (N ^ 4 * cbern) * Real.rpow N (-(β + 4)) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hrpow_pos)
          exact mul_le_mul_of_nonneg_right hcard_le_N4 hcbern_nonneg
      _ = cbern * (Real.rpow N 4 * Real.rpow N (-(β + 4))) := by rw [hN4_rpow]; ring
      _ = cbern * Real.rpow N (-β) := by rw [hrpow_combine]
  have hUnion' :
      bernoulliEventProb p
          (fun Omega3 =>
            ∀ w1 w2 : Fin n₁ × Fin n₂,
              |quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2| ≤
                Cbern * rawTwoTerm) ≥
        1 - cbern * Real.rpow N (-β) := by
    have hge :
        (1 : ℝ) - cbern * Real.rpow N (-β) ≤
          1 - ((Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * cbern) *
              Real.rpow N (-(β + 4)) := by linarith [hCardFail]
    exact le_trans hge hUnion
  -- weaken raw two-term to the target (μ-)scale (absorb Cfro/Centry into Cmax)
  have hRawTwoTerm_le : Cbern * rawTwoTerm ≤ Cbern * (Cmax * targetTwoTerm) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hCbern)
    have hlogfactor_nonneg : 0 ≤ Real.sqrt (((β + 4) * Real.log N) / p) := Real.sqrt_nonneg _
    have hlogdiv_nonneg : 0 ≤ ((β + 4) * Real.log N) / p := by
      have hlogN : 0 ≤ Real.log N := by
        apply Real.log_nonneg; rw [hN]
        have : 1 ≤ max n₁ n₂ := le_trans hn₁ (Nat.le_max_left _ _)
        exact_mod_cast this
      positivity
    have hfrobRaw_eq : frobScaleRaw = Cfro * frobScaleTight := by
      rw [hfrobScaleRaw, hfrobScaleTight]; ring
    have hentryRaw_eq : entryScaleRaw = Centry * entryScaleTight := by
      rw [hentryScaleRaw, hentryScaleTight]; ring
    have hfro_le : Cfro ≤ Cmax := le_max_left _ _
    have hcentry_le : Centry ≤ Cmax := le_max_right _ _
    have hfrob_le : frobScaleRaw ≤ Cmax * frobScaleTight := by
      rw [hfrobRaw_eq]; exact mul_le_mul_of_nonneg_right hfro_le hfrobScaleTight_nonneg
    have hentry_le : entryScaleRaw ≤ Cmax * entryScaleTight := by
      rw [hentryRaw_eq]; exact mul_le_mul_of_nonneg_right hcentry_le hentryScaleTight_nonneg
    calc rawTwoTerm
        = Real.sqrt (((β + 4) * Real.log N) / p) * frobScaleRaw +
            (((β + 4) * Real.log N) / p) * entryScaleRaw := hrawTwoTerm
      _ ≤ Real.sqrt (((β + 4) * Real.log N) / p) * (Cmax * frobScaleTight) +
            (((β + 4) * Real.log N) / p) * (Cmax * entryScaleTight) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hfrob_le hlogfactor_nonneg
            · exact mul_le_mul_of_nonneg_left hentry_le hlogdiv_nonneg
      _ = Cmax * (Real.sqrt (((β + 4) * Real.log N) / p) * frobScaleTight +
            (((β + 4) * Real.log N) / p) * entryScaleTight) := by ring
      _ = Cmax * targetTwoTerm := by rw [htargetTwoTerm]
  -- monotone to QuadraticAllDistinctInnerCoefficientBound at Cbern·Cmax·targetTwoTerm
  have hFinalMono :
      bernoulliEventProb p
          (fun Omega3 =>
            ∀ w1 w2 : Fin n₁ × Fin n₂,
              |quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2| ≤
                Cbern * rawTwoTerm) ≤
        bernoulliEventProb p
          (fun Omega3 =>
            QuadraticAllDistinctInnerCoefficientBound Omega3 S p
              (Cbern * Cmax * targetTwoTerm)) := by
    refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
    intro Omega3 hAll
    intro w1 w2
    have hbnd := hAll w1 w2
    calc |quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2|
        ≤ Cbern * rawTwoTerm := hbnd
      _ ≤ Cbern * (Cmax * targetTwoTerm) := hRawTwoTerm_le
      _ = Cbern * Cmax * targetTwoTerm := by ring
  have hcombined := le_trans hUnion' hFinalMono
  rw [hp, hN] at hcombined ⊢
  simpa [htargetTwoTerm, hfrobScaleTight, hentryScaleTight, mul_assoc] using hcombined
