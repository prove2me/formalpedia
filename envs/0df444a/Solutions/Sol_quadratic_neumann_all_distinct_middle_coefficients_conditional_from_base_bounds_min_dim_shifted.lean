-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds_min_dim_shifted
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-02T15:40:20.808421+00:00
-- url     : https://prove2.me/submissions/69536e3c-760e-41e8-8a4f-c0333b2078b6

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-!
Sound `μ₁`-explicit, `min(n₁,n₂)`-denominator conditional combiner for the
all-distinct middle coefficient bound of the quadratic Neumann term — the second
de la Peña decoupling layer over the independent `Ω₂` sample (CR §6.3, Lemma 6.8
eq (6.22)/(6.23)).

For a fixed `Ω₃` on the inner-coefficient event, the middle coefficient
`H_{ω₁}` is the scalar centered sampling fluctuation (over `Ω₂`) of the
conditional middle base matrix.  This node packages the shifted-density two-term
Bernstein tail + the single-coordinate cardinality union, exactly mirroring the
banked inner combiner
`quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_shifted`,
but with the free scale `innerBound` (the `‖E‖_∞` input of eq (6.22)) in place of
the sign-matrix scale, and the single outer index `ω₁` (cardinality `n₁n₂ ≤ N²`).

Source: Candès--Recht 2008, §6.3, Lemma 6.8 eqs (6.22)--(6.23); the `‖E‖_∞`
estimate preceding Lemma 6.8.
-/

namespace MatrixCompletion

/-- The post-Bernstein two-term scalar scale at the shifted exponent `(β+4)`,
with the free `innerBound` scale, is bounded by `(Cfro+Centry)·innerBound·λ^{-1/2}`
under the `λ`-density proviso.  Identical to the inner absorption with the
sign-matrix scale `μ₁√(r/(n₁n₂))` replaced by the free `innerBound`. -/
private lemma mid_two_term_absorb
    {β lam : ℝ} {n₁ n₂ r m : ℕ} {μ₀ innerBound Centry Cfro : ℝ}
    (hβ : 2 < β) (hlam : 1 ≤ lam)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hib : 0 ≤ innerBound)
    (hCentry : 0 < Centry) (hCfro : 0 < Cfro)
    (hm_pos : 0 < (m : ℝ))
    (hdensity :
      (m : ℝ) ≥
        lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
          (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
            ((β + 4) * Real.log (↑(max n₁ n₂)))) :
    Real.sqrt
          (((β + 4) * Real.log (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * innerBound *
            Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂))))) +
      (((β + 4) * Real.log (↑(max n₁ n₂))) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Centry * innerBound * μ₀ *
            ((r : ℝ) / (↑(min n₁ n₂)))) ≤
      (Cfro + Centry) * innerBound *
          Real.rpow lam (-((1 : ℝ) / 2)) := by
  set N : ℕ := max n₁ n₂ with hN
  set d : ℕ := min n₁ n₂ with hd
  have hN_pos_nat : 0 < N := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hd_pos_nat : 0 < d := lt_min hn₁ hn₂
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hnprod_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hlam_pos : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_ge_one
  have hβ4_pos : 0 < β + 4 := by linarith
  have hp_pos : 0 < (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  -- The energy quantity `A = μ₀ N r (β+4) logN / m`.
  set A : ℝ := (μ₀ * (N : ℝ) * (r : ℝ) * ((β + 4) * Real.log (N : ℝ))) / (m : ℝ)
    with hA
  have hA_nonneg : 0 ≤ A := by rw [hA]; positivity
  -- density gives A ≤ 1/lam, via μ₀^{4/3}, r^{4/3} ≥ μ₀ r.
  have hrpow_mu0 : μ₀ ≤ Real.rpow μ₀ ((4 : ℝ) / 3) := by
    calc μ₀ = Real.rpow μ₀ 1 := (Real.rpow_one μ₀).symm
      _ ≤ Real.rpow μ₀ ((4:ℝ)/3) := by
          apply Real.rpow_le_rpow_of_exponent_le hμ₀
          norm_num
  have hrpow_r : (r : ℝ) ≤ Real.rpow (r : ℝ) ((4 : ℝ) / 3) := by
    calc (r : ℝ) = Real.rpow (r : ℝ) 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow (r : ℝ) ((4:ℝ)/3) := by
          apply Real.rpow_le_rpow_of_exponent_le hr_ge_one
          norm_num
  have hdensity_weak :
      lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β + 4) * Real.log (N : ℝ)) ≤ (m : ℝ) := by
    have hbase_nonneg :
        0 ≤ lam * (N : ℝ) * ((β + 4) * Real.log (N : ℝ)) := by positivity
    have hstep :
        lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β + 4) * Real.log (N : ℝ)) ≤
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) * (N : ℝ) *
            Real.rpow (r : ℝ) ((4 : ℝ) / 3) * ((β + 4) * Real.log (N : ℝ)) := by
      have h1 : μ₀ * (r : ℝ) ≤
          Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r : ℝ) ((4:ℝ)/3) := by
        apply mul_le_mul hrpow_mu0 hrpow_r (le_of_lt hr_pos)
        exact Real.rpow_nonneg hμ₀_pos.le _
      nlinarith [hlog_nonneg, hN_pos.le, hlam_pos.le, hβ4_pos.le, hbase_nonneg,
        Real.rpow_nonneg hμ₀_pos.le ((4:ℝ)/3),
        Real.rpow_nonneg hr_pos.le ((4:ℝ)/3)]
    calc lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β + 4) * Real.log (N : ℝ))
        ≤ lam * Real.rpow μ₀ ((4 : ℝ) / 3) * (N : ℝ) *
            Real.rpow (r : ℝ) ((4 : ℝ) / 3) * ((β + 4) * Real.log (N : ℝ)) := hstep
      _ ≤ (m : ℝ) := by rw [hN] at hdensity ⊢; linarith [hdensity]
  have hA_le_inv_lam : A ≤ lam⁻¹ := by
    rw [hA, div_le_iff₀ hm_pos]
    rw [inv_mul_eq_div, le_div_iff₀ hlam_pos]
    calc μ₀ * (N : ℝ) * (r : ℝ) * ((β + 4) * Real.log (N : ℝ)) * lam
        = lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β + 4) * Real.log (N : ℝ)) := by ring
      _ ≤ (m : ℝ) := hdensity_weak
  -- λ^{-1/2} as a square root of λ⁻¹.
  have hrpow_neg_half : Real.rpow lam (-((1 : ℝ) / 2)) = Real.sqrt lam⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one lam,
      ← Real.rpow_mul hlam_pos.le]
    norm_num
  have hsqrtA_le : Real.sqrt A ≤ Real.rpow lam (-((1 : ℝ) / 2)) := by
    rw [hrpow_neg_half]
    exact Real.sqrt_le_sqrt hA_le_inv_lam
  have hA_le_one : A ≤ 1 := le_trans hA_le_inv_lam (by
    rw [inv_le_one_iff₀]; right; exact hlam)
  have hA_le_sqrtA : A ≤ Real.sqrt A := by
    by_cases hAz : A = 0
    · rw [hAz, Real.sqrt_zero]
    · have hApos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hAz)
      have hsq : A ^ 2 ≤ (Real.sqrt A) ^ 2 := by
        rw [Real.sq_sqrt hA_nonneg]; nlinarith [hA_nonneg, hA_le_one]
      exact (sq_le_sq₀ hA_nonneg (Real.sqrt_nonneg A)).mp hsq
  have hA_le_rpow : A ≤ Real.rpow lam (-((1 : ℝ) / 2)) :=
    le_trans hA_le_sqrtA hsqrtA_le
  -- frobTerm = √((β+4)logN/p) · Cfro innerBound √(μ₀r/d)
  -- = Cfro innerBound · √A.
  have hlog_div_eq :
      ((β + 4) * Real.log (N : ℝ)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        (μ₀ * ((r : ℝ) / (d : ℝ))) = A := by
    rw [hA]
    have hdN : (d : ℝ) * (N : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
      rw [hd, hN]
      have hnat : min n₁ n₂ * max n₁ n₂ = n₁ * n₂ := min_mul_max n₁ n₂
      exact_mod_cast hnat
    field_simp
    nlinarith [hdN, hm_pos, hd_pos, hN_pos, hnprod_pos]
  have hfrob_sqrt :
      Real.sqrt
          (((β + 4) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ))) = Real.sqrt A := by
    rw [← Real.sqrt_mul (by positivity), hlog_div_eq]
  -- FROB TERM ≤ Cfro · innerBound · √A ≤ Cfro · innerBound · λ^{-1/2}
  have hfrob_term :
      Real.sqrt
          (((β + 4) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * innerBound *
            Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ)))) ≤
        Cfro * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) := by
    have hrw :
        Real.sqrt
            (((β + 4) * Real.log (N : ℝ)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ)))) =
          Cfro * innerBound * Real.sqrt A := by
      rw [← hfrob_sqrt]; ring
    rw [hrw]
    have hbase_nonneg : 0 ≤ Cfro * innerBound := by positivity
    exact mul_le_mul_of_nonneg_left hsqrtA_le hbase_nonneg
  -- RANGE TERM = A · Centry · innerBound ≤ Centry · innerBound · λ^{-1/2}
  have hrange_term :
      (((β + 4) * Real.log (N : ℝ)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Centry * innerBound * μ₀ *
            ((r : ℝ) / (d : ℝ))) ≤
        Centry * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) := by
    have hrw :
        (((β + 4) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * innerBound * μ₀ *
              ((r : ℝ) / (d : ℝ))) =
          Centry * innerBound * A := by
      rw [← hlog_div_eq]; ring
    rw [hrw]
    have hbase_nonneg : 0 ≤ Centry * innerBound := by positivity
    exact mul_le_mul_of_nonneg_left hA_le_rpow hbase_nonneg
  -- combine
  have hsum := add_le_add hfrob_term hrange_term
  have hgoal :
      Real.sqrt
            (((β + 4) * Real.log (N : ℝ)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ)))) +
        (((β + 4) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * innerBound * μ₀ *
              ((r : ℝ) / (d : ℝ))) ≤
        (Cfro + Centry) * innerBound *
            Real.rpow lam (-((1 : ℝ) / 2)) := by
    calc _ ≤ Cfro * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) +
              Centry * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) := hsum
      _ = (Cfro + Centry) * innerBound *
            Real.rpow lam (-((1 : ℝ) / 2)) := by ring
  rw [hN, hd] at hgoal ⊢
  convert hgoal using 2

end MatrixCompletion

open MatrixCompletion

/-- Source: Candès--Recht 2008, §6.3, Lemma 6.8 eqs (6.22)--(6.23). -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccond ccond : ℝ, 0 < Ccond ∧ 0 < ccond ∧
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
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (innerBound : ℝ),
        0 ≤ innerBound →
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w1 : Fin n₁ × Fin n₂),
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Centry * innerBound * μ₀ *
              ((r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂))))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Ccond * innerBound) *
                  Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  refine ⟨Cbern * (Cfro + Centry), cbern, by positivity, hcbern, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 _hmLower hmShift Omega3 innerBound hib
    hRep hEntry hFrob
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- per-coordinate two-term tail at shifted exponent (β+4)
  set twoScale : ℝ :=
    Real.sqrt (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
      (Cfro * innerBound *
          Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂))))) +
      (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
        (Centry * innerBound * μ₀ *
            ((r : ℝ) / (↑(min n₁ n₂)))) with htwoScale
  have hβ4 : 2 < β + 4 := by linarith
  have hrpow_nonneg : 0 ≤ Real.rpow lam (-((1 : ℝ) / 2)) :=
    Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le one_pos hlam)) _
  set sc : ℝ := innerBound * Real.rpow lam (-((1 : ℝ) / 2)) with hsc
  -- absorption: twoScale ≤ (Cfro+Centry)·innerBound·λ^{-1/2}
  have hAbsorb : twoScale ≤ (Cfro + Centry) * sc := by
    have hN_pos_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_ge_one : (1 : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast hN_pos_nat
    by_cases hlogzero : Real.log ((max n₁ n₂ : ℕ) : ℝ) = 0
    · -- degenerate N = 1 case: the two-term scale collapses to 0.
      have hz : twoScale = 0 := by
        rw [htwoScale]
        simp only [hlogzero, mul_zero, zero_mul, zero_div, Real.sqrt_zero,
          add_zero]
      rw [hz]
      positivity
    · -- nondegenerate case: density forces m > 0, then apply the absorption lemma.
      have hlog_pos : 0 < Real.log ((max n₁ n₂ : ℕ) : ℝ) :=
        lt_of_le_of_ne (Real.log_nonneg hN_ge_one) (Ne.symm hlogzero)
      have hN_pos : 0 < ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast hN_pos_nat
      have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
      have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
      have hlam_pos : 0 < lam := lt_of_lt_of_le one_pos hlam
      have hβ4_pos : 0 < β + 4 := by linarith
      have hm_pos : 0 < (m : ℝ) := by
        have hRHS_pos :
            0 < lam * Real.rpow μ₀ ((4 : ℝ) / 3) * ((max n₁ n₂ : ℕ) : ℝ) *
                Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
                  ((β + 4) * Real.log ((max n₁ n₂ : ℕ) : ℝ)) := by
          have h1 : 0 < Real.rpow μ₀ ((4:ℝ)/3) := Real.rpow_pos_of_pos hμ₀_pos _
          have h2 : 0 < Real.rpow (r : ℝ) ((4:ℝ)/3) := Real.rpow_pos_of_pos hr_pos _
          positivity
        exact lt_of_lt_of_le hRHS_pos hmShift
      rw [htwoScale, hp, hsc]
      refine le_of_le_of_eq
        (mid_two_term_absorb hβ hlam hn₁ hn₂ hr hμ₀ hib hCentry hCfro hm_pos
          hmShift) ?_
      ring
  -- raw Bernstein tail per coordinate
  have hPair :
      ∀ w1 : Fin n₁ × Fin n₂,
        bernoulliEventProb p
            (fun Omega2 =>
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                (Cbern * (Cfro + Centry)) * sc) ≥
          1 - cbern * Real.rpow (↑(max n₁ n₂)) (-(β + 4)) := by
    intro w1
    have hRep' :
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
          (fun Omega =>
              quadraticAllDistinctMiddleCoefficient Omega Omega3 S p w1) Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega p
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)) := by
      intro Omega; simpa [hp] using hRep Omega w1
    have hRaw :=
      hBernstein (β + 4) hβ4 n₁ n₂ m hn₁ hn₂ hm
        (fun Omega => quadraticAllDistinctMiddleCoefficient Omega Omega3 S p w1)
        (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)
        (Centry * innerBound * μ₀ *
            ((r : ℝ) / (↑(min n₁ n₂))))
        (Cfro * innerBound *
            Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))))
        hRep' (hEntry w1) (hFrob w1)
    -- hRaw bounds |Coeff| by Cbern·twoScale.  Weaken to (Cbern·(Cfro+Centry))·sc.
    have hmono :
        bernoulliEventProb p
            (fun Omega2 =>
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                Cbern * twoScale) ≤
          bernoulliEventProb p
            (fun Omega2 =>
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                (Cbern * (Cfro + Centry)) * sc) := by
      refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
      intro Omega2 hle
      refine le_trans hle ?_
      have hCbern_nonneg : 0 ≤ Cbern := le_of_lt hCbern
      have := mul_le_mul_of_nonneg_left hAbsorb hCbern_nonneg
      calc Cbern * twoScale
          ≤ Cbern * ((Cfro + Centry) * sc) := this
        _ = (Cbern * (Cfro + Centry)) * sc := by ring
    have hRaw' :
        bernoulliEventProb p
            (fun Omega2 =>
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                Cbern * twoScale) ≥
          1 - cbern * Real.rpow (↑(max n₁ n₂)) (-(β + 4)) := by
      simpa [hp, htwoScale, mul_assoc] using hRaw
    exact le_trans hRaw' hmono
  -- single-coordinate union bound (cardinality factor)
  have hUnion :=
    bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
      (Cbern * (Cfro + Centry)) cbern (by positivity) hcbern
      p sc
      (Real.rpow (↑(max n₁ n₂)) (-(β + 4)))
      hp_nonneg hp_le_one n₁ n₂
      (fun w1 Omega2 => quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1)
      hPair
  -- bound the cardinality failure factor by N^{-β}
  have hCardFail :
      ((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cbern) *
          Real.rpow (↑(max n₁ n₂)) (-(β + 4)) ≤
        cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hN_pos_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_ge_one : (1 : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast hN_pos_nat
    -- card = n₁ n₂ ≤ N²
    have hcard_eq :
        (Fintype.card (Fin n₁ × Fin n₂) : ℝ) =
          (n₁ : ℝ) * (n₂ : ℝ) := by
      simp [Fintype.card_prod, Fintype.card_fin]
    have hprod_le_N2 : (n₁ : ℝ) * (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) ^ 2 := by
      have h1 : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_left n₁ n₂
      have h2 : (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_right n₁ n₂
      nlinarith [Nat.cast_nonneg (α := ℝ) n₁, Nat.cast_nonneg (α := ℝ) n₂,
        le_trans zero_le_one hN_ge_one]
    have hcard_le_N2 :
        (Fintype.card (Fin n₁ × Fin n₂) : ℝ) ≤
          ((max n₁ n₂ : ℕ) : ℝ) ^ 2 := by
      rw [hcard_eq]; exact hprod_le_N2
    have hN_pos : 0 < ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast hN_pos_nat
    have hN2_rpow : ((max n₁ n₂ : ℕ) : ℝ) ^ 2 = Real.rpow (↑(max n₁ n₂)) 2 := by
      have := Real.rpow_natCast ((max n₁ n₂ : ℕ) : ℝ) 2
      simpa using this.symm
    have hrpow_combine :
        Real.rpow (↑(max n₁ n₂)) 2 * Real.rpow (↑(max n₁ n₂)) (-(β + 4)) =
          Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
      rw [show Real.rpow (↑(max n₁ n₂)) 2 = (↑(max n₁ n₂) : ℝ) ^ (2 : ℝ) from rfl,
        show Real.rpow (↑(max n₁ n₂)) (-(β + 4)) =
          (↑(max n₁ n₂) : ℝ) ^ (-(β + 4) : ℝ) from rfl,
        show Real.rpow (↑(max n₁ n₂)) (-(β + 2)) =
          (↑(max n₁ n₂) : ℝ) ^ (-(β + 2) : ℝ) from rfl,
        ← Real.rpow_add hN_pos]
      congr 1
      ring
    have hrpow_pos : 0 < Real.rpow (↑(max n₁ n₂)) (-(β + 4)) :=
      Real.rpow_pos_of_pos hN_pos _
    have hcbern_nonneg : 0 ≤ cbern := le_of_lt hcbern
    -- N^{-(β+2)} ≤ N^{-β}
    have hbeta_shift :
        Real.rpow (↑(max n₁ n₂)) (-(β + 2)) ≤ Real.rpow (↑(max n₁ n₂)) (-β) := by
      apply Real.rpow_le_rpow_of_exponent_le hN_ge_one
      linarith
    calc ((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cbern) *
            Real.rpow (↑(max n₁ n₂)) (-(β + 4))
        ≤ (((max n₁ n₂ : ℕ) : ℝ) ^ 2 * cbern) *
            Real.rpow (↑(max n₁ n₂)) (-(β + 4)) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hrpow_pos)
          exact mul_le_mul_of_nonneg_right hcard_le_N2 hcbern_nonneg
      _ = cbern * (Real.rpow (↑(max n₁ n₂)) 2 *
            Real.rpow (↑(max n₁ n₂)) (-(β + 4))) := by rw [hN2_rpow]; ring
      _ = cbern * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by rw [hrpow_combine]
      _ ≤ cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
          exact mul_le_mul_of_nonneg_left hbeta_shift hcbern_nonneg
  -- chain: uniform coordinate event prob ≥ 1 - card·... ≥ 1 - cbern·N^{-β}
  have hUnion' :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w1 : Fin n₁ × Fin n₂,
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                (Cbern * (Cfro + Centry)) * sc) ≥
        1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hge :
        (1 : ℝ) - cbern * Real.rpow (↑(max n₁ n₂)) (-β) ≤
          1 - ((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cbern) *
              Real.rpow (↑(max n₁ n₂)) (-(β + 4)) := by linarith [hCardFail]
    exact le_trans hge hUnion
  -- monotone to QuadraticAllDistinctMiddleCoefficientBound
  have hFinalMono :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w1 : Fin n₁ × Fin n₂,
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                (Cbern * (Cfro + Centry)) * sc) ≤
        bernoulliEventProb p
          (fun Omega2 =>
            QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
              ((Cbern * (Cfro + Centry) * innerBound) *
                Real.rpow lam (-((1 : ℝ) / 2)))) := by
    refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
    intro Omega2 hAll
    intro w1
    have hbnd := hAll w1
    calc |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1|
        ≤ (Cbern * (Cfro + Centry)) * sc := hbnd
      _ = (Cbern * (Cfro + Centry) * innerBound) *
            Real.rpow lam (-((1 : ℝ) / 2)) := by rw [hsc]; ring
  have hcombined := le_trans hUnion' hFinalMono
  simpa [hp, mul_assoc] using hcombined
