-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_from_inner_coefficient_bound_min_dim_shifted
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-02T15:42:50.264888+00:00
-- url     : https://prove2.me/submissions/aba15f5b-8bdd-4d0e-b956-c547b025c2b6

import Theorems.Thm_quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds_min_dim_shifted
import Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
import Theorems.Thm_bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
import Mathlib.Tactic

open MatrixCompletion

/-!
Sound `μ₁`-explicit, `min(n₁,n₂)`-denominator restatement of the second
de la Peña decoupling step (CR §6.3, Lemma 6.8 eqs (6.22)--(6.23)).

Given the `μ₁`-explicit inner `Ω₃` event at scale
`Cinner·μ₁·√(r/(n₁n₂))·λ^{-1/2}`, this node reduces — through the product-probability
pair lift — onto:
  * the conditional `Ω₂` combiner `..._middle_coefficients_conditional_from_base_bounds_min_dim_shifted`
    (node 2), specialised with `innerBound = Cinner·μ₁·√(r/(n₁n₂))·λ^{-1/2}`;
  * the `min`-denominator middle base suppliers (node 1);
  * the Proved middle fluctuation identity.
The output pair `(Ω₂,Ω₃)` middle coefficient bound is at scale
`(Cstep·Cinner·μ₁·√(r/(n₁n₂)))·λ^{-1}`.

Source: Candès--Recht 2008, §6.3, Lemma 6.8 eqs (6.22)--(6.23).
-/

theorem solution :
    ∃ Cstep cstep : ℝ, 0 < Cstep ∧ 0 < cstep ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              ((β + 4) * Real.log (↑(max n₁ n₂))) →
        ∀ Cinner cinner : ℝ, 0 < Cinner → 0 < cinner →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cstep * Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-1))) ≥
          1 - (cstep + cinner) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  -- Node 1: the min-dim middle base suppliers (constants Centry, Cfro).
  rcases quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim with
    ⟨Centry, hCentry, hEntrySup⟩
  rcases quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim with
    ⟨Cfro, hCfro, hFrobNorm⟩
  -- Node 2: the conditional Ω₂ combiner specialised to these constants.
  rcases quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds_min_dim_shifted
      Centry Cfro hCentry hCfro with
    ⟨Ccond, ccond, hCcond, hccond, hCombiner⟩
  refine ⟨Ccond, ccond, hCcond, hccond, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hmShift Cinner cinner hCinner hcinner
    hInnerEvent
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- the μ₁-explicit inner scale that plays the role of `innerBound` in node 2.
  set innerScale : ℝ :=
    (Cinner * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      Real.rpow lam (-((1 : ℝ) / 2)) with hinnerScale
  have hlam_pos : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hμ₁_pos : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hCinner_pos : 0 < Cinner := hCinner
  have hrpow_neg_half_nonneg : 0 ≤ Real.rpow lam (-((1 : ℝ) / 2)) :=
    Real.rpow_nonneg hlam_pos.le _
  have hinnerScale_nonneg : 0 ≤ innerScale := by
    rw [hinnerScale]; positivity
  -- λ^{-1/2} · λ^{-1/2} = λ^{-1}
  have hrpow_half_sq :
      Real.rpow lam (-((1 : ℝ) / 2)) * Real.rpow lam (-((1 : ℝ) / 2)) =
        Real.rpow lam (-1) := by
    have h := (Real.rpow_add hlam_pos (-((1 : ℝ) / 2)) (-((1 : ℝ) / 2))).symm
    rw [show (-((1 : ℝ) / 2)) + (-((1 : ℝ) / 2)) = (-1 : ℝ) by norm_num] at h
    exact h
  -- failure scale for the pair lift.
  set fscale : ℝ := Real.rpow (↑(max n₁ n₂)) (-β) with hfscale
  have hfscale_nonneg : 0 ≤ fscale := by
    rw [hfscale]
    have hN_pos_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_pos : 0 < ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast hN_pos_nat
    exact (Real.rpow_pos_of_pos hN_pos _).le
  have hcCond_scale_nonneg : 0 ≤ ccond * fscale := by positivity
  -- 0 ≤ p ≤ 1
  have hp_nonneg : 0 ≤ p := by
    rw [hp]; positivity
  have hp_le_one : p ≤ 1 := by
    rw [hp, div_le_one (by positivity)]
    have : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by exact_mod_cast hm
    simpa using this
  -- the conditional bound for each Ω₃ on the inner event, via node 2.
  have hCondBound :
      ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerScale →
        bernoulliEventProb p
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
                ((Ccond * Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-1))) ≥
          1 - ccond * fscale := by
    intro Omega3 hInner
    -- middle fluctuation identity (Proved).
    have hRep :
        ∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w1 : Fin n₁ × Fin n₂),
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2 p
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)) := by
      intro Omega2 w1
      exact quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
        Omega2 Omega3 S p w1
    -- node 1 base bounds, instantiated with innerBound = innerScale.
    have hEntry :
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Centry * innerScale * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
      intro w1
      exact hEntrySup n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerScale
        hinnerScale_nonneg hInner w1
    have hFrob :
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Cfro * innerScale *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
      intro w1
      exact hFrobNorm n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerScale
        hinnerScale_nonneg hInner w1
    -- apply node 2.
    have hCond :=
      hCombiner β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hmShift Omega3 innerScale
        hinnerScale_nonneg hRep hEntry hFrob
    -- rewrite the node-2 output scale `Ccond·innerScale·λ^{-1/2}` into the target.
    have hscale_eq :
        (Ccond * innerScale) * Real.rpow lam (-((1 : ℝ) / 2)) =
          (Ccond * Cinner * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.rpow lam (-1) := by
      rw [hinnerScale]
      calc
        Ccond *
            ((Cinner * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              Real.rpow lam (-((1 : ℝ) / 2))) *
            Real.rpow lam (-((1 : ℝ) / 2))
            = (Ccond * Cinner * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Real.rpow lam (-((1 : ℝ) / 2)) *
                Real.rpow lam (-((1 : ℝ) / 2))) := by ring
          _ = (Ccond * Cinner * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              Real.rpow lam (-1) := by rw [hrpow_half_sq]
    rw [hp, hfscale]
    rw [hscale_eq] at hCond
    exact hCond
  -- inner marginal event hypothesis in the right shape.
  have hMarg :
      bernoulliEventProb p
          (fun Omega3 =>
            QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerScale) ≥
        1 - cinner * fscale := by
    rw [hp, hinnerScale, hfscale]
    exact hInnerEvent
  -- assemble via the generic product-probability pair lift.
  have hPair :=
    bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
      p cinner ccond fscale
      (fun Omega3 =>
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerScale)
      (fun Omega2 Omega3 =>
        QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
          ((Ccond * Cinner * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.rpow lam (-1)))
      hp_nonneg hp_le_one hcCond_scale_nonneg hMarg hCondBound
  -- conclude.
  rw [hp, hfscale]
  have hfinal :
      bernoulliPairEventProb p
          (fun Omega2 Omega3 =>
            QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
              ((Ccond * Cinner * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                Real.rpow lam (-1))) ≥
        1 - (ccond + cinner) * fscale := hPair
  rw [hp, hfscale] at hfinal
  exact hfinal
