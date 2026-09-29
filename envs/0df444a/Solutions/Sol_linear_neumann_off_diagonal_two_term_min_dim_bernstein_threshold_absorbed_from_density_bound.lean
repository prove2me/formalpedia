-- Prove2me | solution 1 for linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_from_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T10:44:01.497782+00:00
-- url     : https://prove2.me/submissions/00d9e68f-fd37-4320-aacb-d4b5277aff69

import Definitions.Def_linear_neumann_offdiag_bernstein
import Mathlib.Tactic

open MatrixCompletion

open MatrixCompletion

namespace MatrixCompletion

private lemma beta_shift_le_two_beta {β : ℝ} (hβ : 2 < β) :
    β + 2 ≤ 2 * β := by
  linarith

private lemma nat_min_mul_max_cast
    {n₁ n₂ : ℕ} :
    ((min n₁ n₂ : ℕ) : ℝ) * ((max n₁ n₂ : ℕ) : ℝ) =
      (n₁ : ℝ) * (n₂ : ℝ) := by
  have hnat : min n₁ n₂ * max n₁ n₂ = n₁ * n₂ := by
    exact min_mul_max n₁ n₂
  exact_mod_cast hnat

private lemma sqrt_mul_sqrt_le_sqrt_mul_of_nonneg
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (habcd : a * b ≤ c * d) :
    Real.sqrt a * Real.sqrt b ≤ Real.sqrt c * Real.sqrt d := by
  have hleft_nonneg : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
  have hright_nonneg : 0 ≤ Real.sqrt c * Real.sqrt d := by positivity
  refine (sq_le_sq₀ hleft_nonneg hright_nonneg).mp ?_
  rw [mul_pow, mul_pow]
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc, Real.sq_sqrt hd]
  exact habcd

private lemma linear_neumann_offdiag_frobenius_scalar_absorption
    {β : ℝ} {n₁ n₂ r m : ℕ} {μ₀ : ℝ}
    (hβ : 2 < β) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hm_pos : 0 < (m : ℝ)) :
    Real.sqrt
        (((β + 2) * Real.log (↑(max n₁ n₂))) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ≤
        2 *
          Real.sqrt
            ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  let N : ℕ := max n₁ n₂
  let d : ℕ := min n₁ n₂
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hd_pos_nat : 0 < d := by
    dsimp [d]
    exact lt_min hn₁ hn₂
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN_pos_nat)
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hnprod_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hden_pos : 0 < (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  have hβ_nonneg : 0 ≤ β := by linarith
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_ge_one
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hleft₁_nonneg :
      0 ≤ ((β + 2) * Real.log (N : ℝ)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    have hβ2_nonneg : 0 ≤ β + 2 := by linarith
    positivity
  have hleft₂_nonneg :
      0 ≤ μ₀ * (r : ℝ) / (d : ℝ) := by positivity
  have hright_nonneg :
      0 ≤ ((μ₀ * (N : ℝ) * (r : ℝ) *
            (β * Real.log (N : ℝ))) / (m : ℝ)) := by positivity
  have hprod_le :
      (((β + 2) * Real.log (N : ℝ)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (μ₀ * (r : ℝ) / (d : ℝ)) ≤
          4 *
            ((μ₀ * (N : ℝ) * (r : ℝ) *
              (β * Real.log (N : ℝ))) / (m : ℝ)) := by
    have hshift : β + 2 ≤ 4 * β := by
      have h := beta_shift_le_two_beta hβ
      nlinarith
    have hmain :
        ((β + 2) * Real.log (N : ℝ)) *
            ((n₁ : ℝ) * (n₂ : ℝ)) *
            (μ₀ * (r : ℝ)) ≤
          4 *
            (μ₀ * (N : ℝ) * (r : ℝ) *
              (β * Real.log (N : ℝ))) *
            (d : ℝ) := by
      have hdn :
          (d : ℝ) * (N : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
        dsimp [d, N]
        exact nat_min_mul_max_cast
      have hcommon_nonneg :
          0 ≤ Real.log (N : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) *
              (μ₀ * (r : ℝ)) := by positivity
      have hmul :=
        mul_le_mul_of_nonneg_right hshift hcommon_nonneg
      nlinarith [hmul, hdn]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hm_pos
    have hd_nonneg : 0 ≤ (d : ℝ) := le_of_lt hd_pos
    field_simp [hm_pos.ne', hnprod_pos.ne', hd_pos.ne', hr_pos.ne']
    have hsimple :
        (β + 2) * Real.log (N : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) * μ₀ ≤
          4 * β * Real.log (N : ℝ) * ((d : ℝ) * (N : ℝ)) * μ₀ := by
      have hdn :
          (d : ℝ) * (N : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
        dsimp [d, N]
        exact nat_min_mul_max_cast
      have hcommon_nonneg :
          0 ≤ Real.log (N : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) * μ₀ := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hshift hcommon_nonneg
      nlinarith [hmul, hdn]
    nlinarith
  have hsqrt_le :
      Real.sqrt
          (((β + 2) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        Real.sqrt (μ₀ * (r : ℝ) / (d : ℝ)) ≤
          Real.sqrt 4 *
            Real.sqrt
              ((μ₀ * (N : ℝ) * (r : ℝ) *
                (β * Real.log (N : ℝ))) / (m : ℝ)) := by
    exact sqrt_mul_sqrt_le_sqrt_mul_of_nonneg hleft₁_nonneg hleft₂_nonneg
      (by norm_num : (0 : ℝ) ≤ 4) hright_nonneg hprod_le
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
  simpa [N, d, hsqrt4] using hsqrt_le

private lemma linear_neumann_offdiag_range_scalar_absorption
    {β : ℝ} {n₁ n₂ r m : ℕ} {μ₀ : ℝ}
    (hβ : 2 < β) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hm_pos : 0 < (m : ℝ))
    (hdensity :
      (m : ℝ) ≥
        ((8 : ℝ) / 3) * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂)))) :
    (((β + 2) * Real.log (↑(max n₁ n₂))) /
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ≤
        2 *
          Real.sqrt
            ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  let N : ℕ := max n₁ n₂
  let d : ℕ := min n₁ n₂
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hd_pos_nat : 0 < d := by
    dsimp [d]
    exact lt_min hn₁ hn₂
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN_pos_nat)
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hnprod_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hβ_nonneg : 0 ≤ β := by linarith
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_ge_one
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  let A : ℝ :=
    (μ₀ * (N : ℝ) * (r : ℝ) * (β * Real.log (N : ℝ))) / (m : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA_le_one : A ≤ 1 := by
    dsimp [A]
    have hden :
        ((8 : ℝ) / 3) *
            (μ₀ * (N : ℝ) * (r : ℝ) *
              (β * Real.log (N : ℝ))) ≤ (m : ℝ) := by
      simpa [N, mul_assoc, mul_left_comm, mul_comm] using hdensity
    by_cases hbase :
        μ₀ * (N : ℝ) * (r : ℝ) * (β * Real.log (N : ℝ)) = 0
    · simp [hbase]
    · have hbase_pos :
          0 < μ₀ * (N : ℝ) * (r : ℝ) *
            (β * Real.log (N : ℝ)) := by
        have hbase_nonneg :
            0 ≤ μ₀ * (N : ℝ) * (r : ℝ) *
              (β * Real.log (N : ℝ)) := by positivity
        exact lt_of_le_of_ne hbase_nonneg (Ne.symm hbase)
      have hm_pos' : 0 < (m : ℝ) := hm_pos
      have hbase_le_m : μ₀ * (N : ℝ) * (r : ℝ) *
            (β * Real.log (N : ℝ)) ≤ (m : ℝ) := by
        have hfactor : (1 : ℝ) ≤ (8 : ℝ) / 3 := by norm_num
        nlinarith
      exact (div_le_one hm_pos').mpr hbase_le_m
  have hA_le_sqrt : A ≤ Real.sqrt A := by
    by_cases hA_zero : A = 0
    · simp [hA_zero]
    · have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA_zero)
      have hsq : A ^ 2 ≤ (Real.sqrt A) ^ 2 := by
        rw [Real.sq_sqrt hA_nonneg]
        nlinarith
      exact (sq_le_sq₀ hA_nonneg (Real.sqrt_nonneg A)).mp hsq
  have hterm_le_twoA :
      (((β + 2) * Real.log (N : ℝ)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (μ₀ * (r : ℝ) / (d : ℝ)) ≤ 2 * A := by
    have hshift : β + 2 ≤ 2 * β := beta_shift_le_two_beta hβ
    have hdn :
        (d : ℝ) * (N : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
      dsimp [d, N]
      exact nat_min_mul_max_cast
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    dsimp [A]
    field_simp [hm_pos.ne', hnprod_pos.ne', hd_pos.ne', hr_pos.ne']
    have hcommon_nonneg :
        0 ≤ Real.log (N : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) *
            (μ₀ * (r : ℝ)) := by positivity
    have hsimple :
        (β + 2) * Real.log (N : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) * μ₀ ≤
          2 * β * Real.log (N : ℝ) * ((d : ℝ) * (N : ℝ)) * μ₀ := by
      have hdn :
          (d : ℝ) * (N : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
        dsimp [d, N]
        exact nat_min_mul_max_cast
      have hcommon_nonneg' :
          0 ≤ Real.log (N : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) * μ₀ := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hshift hcommon_nonneg'
      nlinarith [hmul, hdn]
    nlinarith
  have htwoA_le : 2 * A ≤ 2 * Real.sqrt A := by
    nlinarith
  exact le_trans (by simpa [N, d] using hterm_le_twoA) (by
    simpa [A, N] using htwoA_le)

end MatrixCompletion

/-- Source: Candès--Recht 2008, Section 6.2, PDF p. 28, equation (6.17)
and the paragraph immediately following it.  This solution proves the
post-Bernstein scalar absorption under the density proviso used there. -/
theorem solution
    (Ctwo Centry Cfro : ℝ) :
    0 < Ctwo → 0 < Centry → 0 < Cfro →
    ∃ Ccoef : ℝ, 0 < Ccoef ∧
      ∀ Ccoef' : ℝ, Ccoef ≤ Ccoef' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          ((8 : ℝ) / 3) * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        Ctwo *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Centry * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) ≤
          Ccoef' * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  intro hCtwo hCentry hCfro
  refine ⟨max 1 (2 * Ctwo * (Cfro + Centry)), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro Ccoef' hCcoef' β hβ n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr _hm hμ₀ hμ₁ hdensity
    let N : ℕ := max n₁ n₂
    by_cases hlog_zero : Real.log (N : ℝ) = 0
    · have hlog_zero' : Real.log ((max n₁ n₂ : ℕ) : ℝ) = 0 := by
        simpa [N] using hlog_zero
      have hlog_zero'' : Real.log (max (n₁ : ℝ) (n₂ : ℝ)) = 0 := by
        simpa [Nat.cast_max] using hlog_zero'
      simp [hlog_zero'']
    have hN_pos_nat : 0 < N := by
      dsimp [N]
      exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hN_pos_nat)
    have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_ge_one
    have hm_pos : 0 < (m : ℝ) := by
      have hβ_pos : 0 < β := by linarith
      have hbase_pos :
          0 <
            μ₀ * (N : ℝ) * (r : ℝ) *
              (β * Real.log (N : ℝ)) := by
        have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le zero_lt_one hμ₀
        have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
        have hr_pos_real : 0 < (r : ℝ) := by exact_mod_cast hr
        have hlog_pos : 0 < Real.log (N : ℝ) :=
          lt_of_le_of_ne hlog_nonneg (Ne.symm hlog_zero)
        positivity
      have htarget_pos :
          0 <
            ((8 : ℝ) / 3) * μ₀ * (N : ℝ) * (r : ℝ) *
              (β * Real.log (N : ℝ)) := by positivity
      have hdensity' :
          (m : ℝ) ≥
            ((8 : ℝ) / 3) * μ₀ * (N : ℝ) * (r : ℝ) *
              (β * Real.log (N : ℝ)) := by
        simpa [N] using hdensity
      exact lt_of_lt_of_le htarget_pos hdensity'
    have hcommon_nonneg :
        0 ≤ μ₁ *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by positivity
    have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
    have hscale_nonneg :
        0 ≤ Real.sqrt
          ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
      exact Real.sqrt_nonneg _
    have hfrob :=
      linear_neumann_offdiag_frobenius_scalar_absorption
        (β := β) (n₁ := n₁) (n₂ := n₂) (r := r) (m := m) (μ₀ := μ₀)
        hβ hn₁ hn₂ hr hμ₀ hm_pos
    have hrange :=
      linear_neumann_offdiag_range_scalar_absorption
        (β := β) (n₁ := n₁) (n₂ := n₂) (r := r) (m := m) (μ₀ := μ₀)
        hβ hn₁ hn₂ hr hμ₀ hm_pos hdensity
    have hCcoef_nonneg :
        0 ≤ Ccoef' := by
      have : (0 : ℝ) ≤ max 1 (2 * Ctwo * (Cfro + Centry)) := by
        exact le_trans zero_le_one (le_max_left _ _)
      exact le_trans this hCcoef'
    have hconstant :
        2 * Ctwo * (Cfro + Centry) ≤ Ccoef' := by
      exact le_trans (le_max_right _ _) hCcoef'
    have hCentry_nonneg : 0 ≤ Centry := le_of_lt hCentry
    have hCfro_nonneg : 0 ≤ Cfro := le_of_lt hCfro
    have hCtwo_nonneg : 0 ≤ Ctwo := le_of_lt hCtwo
    let common : ℝ :=
      μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    let targetScale : ℝ :=
      Real.sqrt
        ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
    have hcommon_nonneg' : 0 ≤ common := by
      dsimp [common]
      positivity
    have htargetScale_nonneg : 0 ≤ targetScale := by
      dsimp [targetScale]
      positivity
    have hfrob_scaled :
        Real.sqrt
            (((β + 2) * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * common *
            Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) ≤
            2 * Cfro * common * targetScale := by
      have h := mul_le_mul_of_nonneg_left hfrob hCfro_nonneg
      have h2 := mul_le_mul_of_nonneg_left h hcommon_nonneg'
      nlinarith
    have hrange_scaled :
        (((β + 2) * Real.log (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * common *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) ≤
            2 * Centry * common * targetScale := by
      have h := mul_le_mul_of_nonneg_left hrange hCentry_nonneg
      have h2 := mul_le_mul_of_nonneg_left h hcommon_nonneg'
      nlinarith
    have hsum :
        Real.sqrt
            (((β + 2) * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * common *
            Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
        (((β + 2) * Real.log (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * common *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) ≤
          2 * (Cfro + Centry) * common * targetScale := by
      nlinarith
    have hsum_scaled :
        Ctwo *
          (Real.sqrt
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Cfro * common *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
          (((β + 2) * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Centry * common *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) ≤
          Ccoef' * common * targetScale := by
      have h := mul_le_mul_of_nonneg_left hsum hCtwo_nonneg
      have hscale_nonneg' : 0 ≤ common * targetScale := by positivity
      nlinarith
    simpa [common, targetScale, mul_assoc, mul_left_comm, mul_comm] using hsum_scaled
