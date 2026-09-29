-- Prove2me | solution 1 for quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T11:21:23.76331+00:00
-- url     : https://prove2.me/submissions/9b6cb734-b7e1-4893-8c52-4fbe5a3052af

import Theorems.Thm_centered_sampling_spectral_event_from_a0_energy_moment
import Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
import Theorems.Thm_quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
import Theorems.Thm_bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open MatrixCompletion

open scoped Classical BigOperators

set_option maxHeartbeats 1000000

/-!
# §6.3 all-distinct centered decoupled brick (Child A) — HONEST four-term scale

The §6.3 analytic content of the fully decoupled all-distinct case (three
independent copies `Ω₁, Ω₂, Ω₃`) at the four-term summary scale `Φ`, as a
TRIPLE event.  This is the HONEST re-derivation: it consumes the honest
four-term middle coefficient pair event (node 2′) which carries the
`√(density)` factor, and maps the resulting FOUR spectral pieces directly into
the fourth summary term `Φ₄` (NOT `Φ₃`), WITHOUT the `nn/M` majorisation.

Composition (all ingredients Proved/banked or Open child stubs):

* the HONEST coefficient entrySup PAIR EVENT over the inner two copies `(Ω₂,Ω₃)`
  (`quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim`)
  bounds `‖H_{Ω₁}‖∞ ≤ Ccoef · fourTerm` via the outer-coefficient bridge;
* node (iv) (`centered_sampling_spectral_event_from_a0_energy_moment`) applied
  to `X = outerCoeffMatrix Ω₂ Ω₃` produces the outer spectral EVENT over `Ω₁`;
* the rep identity
  (`quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation`)
  rewrites the decoupled contribution as
  `centeredSamplingFluctuation Ω₁ p (outerCoeffMatrix Ω₂ Ω₃)` -- NO scalar
  prefactor (this is the all-distinct simplification);
* the honest four-term scale combines with the outer spectral scale to the
  fourth summary term `Φ₄` of `Φ` — the four sub-terms of `fourTerm` expand into
  four spectral pieces `A,B,C,D`, each discharged by a squaring inequality
  against a per-piece multiple of `Φ₄` under the general sample lower bound;
* the outer conditional and inner pair events are combined by the generic
  product-Bernoulli triple lift.

Source: Candès–Recht 2008, §6.3, PDF pp. 33--34, equation (6.23).
-/

namespace MatrixCompletion

/-- Total Bernoulli observation weight is 1. -/
private lemma bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ, Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard : (Finset.univ : Finset α).card = N := by simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α, p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl; intro k hk; ring
    _ = (p + (1 - p)) ^ N := by rw [add_pow]
    _ = 1 := by ring

/-- `y ^ (3/2) = y * √y` for `y ≥ 0`. -/
private lemma rpow_three_halves {y : ℝ} (hy : 0 ≤ y) :
    Real.rpow y ((3 : ℝ) / 2) = y * Real.sqrt y := by
  rcases eq_or_lt_of_le hy with h | h
  · rw [← h]; simp [Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0)]
  · have hrw : y * Real.sqrt y = y ^ (1 : ℝ) * y ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_one]
    rw [hrw, ← Real.rpow_add h]; norm_num

/-- Piece A of the Φ₄ mapping.  Constant `c_A = 4`. -/
private lemma piece_A_le
    (N R M mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef : ℝ)
    (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hmn_pos : 0 < mn)
    (hlog : 0 ≤ logN) (hβ : 2 < β)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hM_pos : 0 < M)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef) :
    (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (Real.sqrt (μ₀ * R / mn) *
            (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn))))))
      ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 4) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) := by
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hbl : 0 ≤ β * logN := by positivity
  have hs2 : 0 ≤ ((β + 2) * logN) / p := by positivity
  have hs4 : 0 ≤ ((β + 4) * logN) / p := by positivity
  set L := (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (Real.sqrt (μ₀ * R / mn) *
            (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn)))))) with hL
  set Rt := ((Ctail * Real.sqrt Cenergy * Ccoef * 4) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)) with hRt
  have hL_nonneg : 0 ≤ L := by rw [hL]; positivity
  have hRt_nonneg : 0 ≤ Rt := by
    rw [hRt]
    have : 0 ≤ Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hL2 : L ^ 2 =
      2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β * logN ^ 3 * μ₀ ^ 2 * μ₁ ^ 2 *
        ((β + 2) * (β + 4)) / M ^ 3 := by
    rw [hL]
    have e1 : Real.sqrt (2 * (β * logN)) ^ 2 = 2 * (β * logN) := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (Cenergy * p * N) ^ 2 = Cenergy * p * N := Real.sq_sqrt (by positivity)
    have e3 : Real.sqrt (((β + 2) * logN) / p) ^ 2 = ((β + 2) * logN) / p := Real.sq_sqrt hs2
    have e4 : Real.sqrt (μ₀ * R / mn) ^ 2 = μ₀ * R / mn := Real.sq_sqrt (by positivity)
    have e5 : Real.sqrt (((β + 4) * logN) / p) ^ 2 = ((β + 4) * logN) / p := Real.sq_sqrt hs4
    have e6 : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
    simp only [mul_pow]
    rw [e1, e2, e3, e4, e5, e6, hp, hnn]
    field_simp
  have hRt2 : Rt ^ 2 =
      16 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 /
        M ^ 3 := by
    rw [hRt]
    have hrp : Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)
        = ((μ₀ * μ₁ * N * R * (β * logN)) / M) *
            Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) :=
      rpow_three_halves (by positivity)
    have e6 : Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) ^ 2
        = (μ₀ * μ₁ * N * R * (β * logN)) / M := Real.sq_sqrt (by positivity)
    have e7 : Real.sqrt Cenergy ^ 2 = Cenergy := Real.sq_sqrt (le_of_lt hCenergy)
    rw [hrp]
    simp only [mul_pow]
    rw [e6, e7]
    field_simp; ring
  have hkey : (β + 2) * (β + 4) ≤ 8 * β ^ 2 * μ₀ * μ₁ := by
    have hμ01 : (1 : ℝ) ≤ μ₀ * μ₁ := by nlinarith [hμ₀, hμ₁, mul_pos hμ₀0 hμ₁0]
    have hbase : (β + 2) * (β + 4) ≤ 8 * β ^ 2 := by nlinarith [hβ, sq_nonneg (β - 2)]
    nlinarith [hbase, hμ01, sq_nonneg β, mul_pos hμ₀0 hμ₁0]
  have hL2_le : L ^ 2 ≤ Rt ^ 2 := by
    rw [hL2, hRt2, div_le_div_iff₀ (by positivity) (by positivity)]
    set mult : ℝ :=
      2 * (Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β * logN ^ 3 * μ₀ ^ 2 * μ₁ ^ 2 * M ^ 3)
      with hmult_def
    have hmult : (0 : ℝ) ≤ mult := by rw [hmult_def]; positivity
    have hscaled := mul_le_mul_of_nonneg_left hkey hmult
    have hLeq :
        2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β * logN ^ 3 * μ₀ ^ 2 * μ₁ ^ 2 *
              ((β + 2) * (β + 4)) * M ^ 3
          = mult * ((β + 2) * (β + 4)) := by rw [hmult_def]; ring
    have hReq :
        16 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 *
              M ^ 3
          = mult * (8 * β ^ 2 * μ₀ * μ₁) := by rw [hmult_def]; ring
    rw [hLeq, hReq]; exact hscaled
  exact le_of_sq_le_sq hL2_le hRt_nonneg

/-- Piece B of the Φ₄ mapping.  Constant `c_B = 7`.  Uses `hmlow2`. -/
private lemma piece_B_le
    (N R M mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef : ℝ)
    (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hmn_pos : 0 < mn)
    (hlog : 0 ≤ logN) (hβ : 2 < β)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hM_pos : 0 < M)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef)
    (hmlow : M ≥ μ₁ ^ 2 * N * R * (β * logN)) :
    (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (Real.sqrt (μ₀ * R / mn) *
            ((((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn))))))
      ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 7) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) := by
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hbl : 0 ≤ β * logN := by positivity
  have hs2 : 0 ≤ ((β + 2) * logN) / p := by positivity
  have hs4 : 0 ≤ ((β + 4) * logN) / p := by positivity
  set L := (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (Real.sqrt (μ₀ * R / mn) *
            ((((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn)))))) with hL
  set Rt := ((Ctail * Real.sqrt Cenergy * Ccoef * 7) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)) with hRt
  have hL_nonneg : 0 ≤ L := by rw [hL]; positivity
  have hRt_nonneg : 0 ≤ Rt := by
    rw [hRt]
    have : 0 ≤ Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hL2 : L ^ 2 =
      2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 4 * R ^ 4 * β * logN ^ 4 * μ₀ ^ 3 * μ₁ ^ 2 *
        ((β + 2) * (β + 4) ^ 2) / M ^ 4 := by
    rw [hL]
    have e1 : Real.sqrt (2 * (β * logN)) ^ 2 = 2 * (β * logN) := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (Cenergy * p * N) ^ 2 = Cenergy * p * N := Real.sq_sqrt (by positivity)
    have e3 : Real.sqrt (((β + 2) * logN) / p) ^ 2 = ((β + 2) * logN) / p := Real.sq_sqrt hs2
    have e4 : Real.sqrt (μ₀ * R / mn) ^ 2 = μ₀ * R / mn := Real.sq_sqrt (by positivity)
    have e6 : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
    simp only [mul_pow]
    rw [e1, e2, e3, e4, e6, hp, hnn]
    field_simp
  have hRt2 : Rt ^ 2 =
      49 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 /
        M ^ 3 := by
    rw [hRt]
    have hrp : Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)
        = ((μ₀ * μ₁ * N * R * (β * logN)) / M) *
            Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) :=
      rpow_three_halves (by positivity)
    have e6 : Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) ^ 2
        = (μ₀ * μ₁ * N * R * (β * logN)) / M := Real.sq_sqrt (by positivity)
    have e7 : Real.sqrt Cenergy ^ 2 = Cenergy := Real.sq_sqrt (le_of_lt hCenergy)
    rw [hrp]
    simp only [mul_pow]
    rw [e6, e7]
    field_simp; ring
  -- key: 2·N·R·logN·(β+2)(β+4)² ≤ 49·M·β²·μ₁
  have hkey : 2 * N * R * logN * ((β + 2) * (β + 4) ^ 2) ≤ 49 * M * β ^ 2 * μ₁ := by
    -- from M ≥ μ₁²·N·R·(β·logN), scale by (49·β²·μ₁ / (μ₁²·β·logN)) implicitly:
    -- 49·M·β²·μ₁ ≥ 49·μ₁²·N·R·(β·logN)·β²·μ₁ = 49·μ₁³·N·R·β³·logN
    have hμ13 : (1 : ℝ) ≤ μ₁ ^ 3 := by nlinarith [hμ₁, sq_nonneg μ₁]
    have hfac : (0 : ℝ) ≤ 49 * β ^ 2 * μ₁ := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmlow hfac
    -- hstep : M · (49β²μ₁) ≥ (μ₁²·N·R·(β·logN)) · (49β²μ₁)
    have hbeta : 2 * ((β + 2) * (β + 4) ^ 2) ≤ 49 * β ^ 3 := by
      nlinarith [hβ, sq_nonneg (β - 2)]
    have hNRl : (0 : ℝ) ≤ N * R * logN := by positivity
    have hbase : 2 * N * R * logN * ((β + 2) * (β + 4) ^ 2)
        ≤ 49 * β ^ 3 * (N * R * logN) := by nlinarith [mul_le_mul_of_nonneg_left hbeta hNRl]
    -- 49·β³·N·R·logN ≤ 49·μ₁³·N·R·β³·logN ≤ 49·M·β²·μ₁
    have hmid : 49 * β ^ 3 * (N * R * logN) ≤ 49 * μ₁ ^ 3 * N * R * β ^ 3 * logN := by
      have hβ3 : (0 : ℝ) ≤ β ^ 3 * (N * R * logN) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ13) hβ3]
    have hend : 49 * μ₁ ^ 3 * N * R * β ^ 3 * logN ≤ 49 * M * β ^ 2 * μ₁ := by
      nlinarith [hstep]
    linarith [hbase, hmid, hend]
  have hL2_le : L ^ 2 ≤ Rt ^ 2 := by
    rw [hL2, hRt2, div_le_div_iff₀ (by positivity) (by positivity)]
    set mult : ℝ :=
      Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 2 * M ^ 3
      with hmult_def
    have hmult : (0 : ℝ) ≤ mult := by rw [hmult_def]; positivity
    have hscaled := mul_le_mul_of_nonneg_left hkey hmult
    have hLeq :
        2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 4 * R ^ 4 * β * logN ^ 4 * μ₀ ^ 3 * μ₁ ^ 2 *
              ((β + 2) * (β + 4) ^ 2) * M ^ 3
          = mult * (2 * N * R * logN * ((β + 2) * (β + 4) ^ 2)) := by rw [hmult_def]; ring
    have hReq :
        49 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 *
              M ^ 4
          = mult * (49 * M * β ^ 2 * μ₁) := by rw [hmult_def]; ring
    rw [hLeq, hReq]; exact hscaled
  exact le_of_sq_le_sq hL2_le hRt_nonneg

/-- Piece C of the Φ₄ mapping.  Constant `c_C = 6`.  Uses `hmlow2`. -/
private lemma piece_C_le
    (N R M mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef : ℝ)
    (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hmn_pos : 0 < mn)
    (hlog : 0 ≤ logN) (hβ : 2 < β)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hM_pos : 0 < M)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef)
    (hmlow : M ≥ μ₁ ^ 2 * N * R * (β * logN)) :
    (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          ((μ₀ * R / mn) *
            (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn))))))
      ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 6) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) := by
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hbl : 0 ≤ β * logN := by positivity
  have hs2 : 0 ≤ ((β + 2) * logN) / p := by positivity
  have hs4 : 0 ≤ ((β + 4) * logN) / p := by positivity
  set L := (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          ((μ₀ * R / mn) *
            (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn)))))) with hL
  set Rt := ((Ctail * Real.sqrt Cenergy * Ccoef * 6) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)) with hRt
  have hL_nonneg : 0 ≤ L := by rw [hL]; positivity
  have hRt_nonneg : 0 ≤ Rt := by
    rw [hRt]
    have : 0 ≤ Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hL2 : L ^ 2 =
      2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 4 * R ^ 4 * β * logN ^ 4 * μ₀ ^ 3 * μ₁ ^ 2 *
        ((β + 2) ^ 2 * (β + 4)) / M ^ 4 := by
    rw [hL]
    have e1 : Real.sqrt (2 * (β * logN)) ^ 2 = 2 * (β * logN) := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (Cenergy * p * N) ^ 2 = Cenergy * p * N := Real.sq_sqrt (by positivity)
    have e4 : Real.sqrt (μ₀ * R / mn) ^ 2 = μ₀ * R / mn := Real.sq_sqrt (by positivity)
    have e5 : Real.sqrt (((β + 4) * logN) / p) ^ 2 = ((β + 4) * logN) / p := Real.sq_sqrt hs4
    have e6 : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
    simp only [mul_pow]
    rw [e1, e2, e4, e5, e6, hp, hnn]
    field_simp
  have hRt2 : Rt ^ 2 =
      36 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 /
        M ^ 3 := by
    rw [hRt]
    have hrp : Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)
        = ((μ₀ * μ₁ * N * R * (β * logN)) / M) *
            Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) :=
      rpow_three_halves (by positivity)
    have e6 : Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) ^ 2
        = (μ₀ * μ₁ * N * R * (β * logN)) / M := Real.sq_sqrt (by positivity)
    have e7 : Real.sqrt Cenergy ^ 2 = Cenergy := Real.sq_sqrt (le_of_lt hCenergy)
    rw [hrp]
    simp only [mul_pow]
    rw [e6, e7]
    field_simp; ring
  have hkey : N * R * logN * ((β + 2) ^ 2 * (β + 4)) ≤ 18 * M * β ^ 2 * μ₁ := by
    have hμ13 : (1 : ℝ) ≤ μ₁ ^ 3 := by nlinarith [hμ₁, sq_nonneg μ₁]
    have hfac : (0 : ℝ) ≤ 18 * β ^ 2 * μ₁ := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmlow hfac
    have hbeta : (β + 2) ^ 2 * (β + 4) ≤ 18 * β ^ 3 := by nlinarith [hβ, sq_nonneg (β - 2)]
    have hNRl : (0 : ℝ) ≤ N * R * logN := by positivity
    have hbase : N * R * logN * ((β + 2) ^ 2 * (β + 4)) ≤ 18 * β ^ 3 * (N * R * logN) := by
      nlinarith [mul_le_mul_of_nonneg_left hbeta hNRl]
    have hβ3 : (0 : ℝ) ≤ β ^ 3 * (N * R * logN) := by positivity
    have hmid : 18 * β ^ 3 * (N * R * logN) ≤ 18 * μ₁ ^ 3 * N * R * β ^ 3 * logN := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ13) hβ3]
    have hend : 18 * μ₁ ^ 3 * N * R * β ^ 3 * logN ≤ 18 * M * β ^ 2 * μ₁ := by nlinarith [hstep]
    linarith [hbase, hmid, hend]
  have hL2_le : L ^ 2 ≤ Rt ^ 2 := by
    rw [hL2, hRt2, div_le_div_iff₀ (by positivity) (by positivity)]
    set mult : ℝ :=
      2 * (Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 2 * M ^ 3)
      with hmult_def
    have hmult : (0 : ℝ) ≤ mult := by rw [hmult_def]; positivity
    have hscaled := mul_le_mul_of_nonneg_left hkey hmult
    have hLeq :
        2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 4 * R ^ 4 * β * logN ^ 4 * μ₀ ^ 3 * μ₁ ^ 2 *
              ((β + 2) ^ 2 * (β + 4)) * M ^ 3
          = mult * (N * R * logN * ((β + 2) ^ 2 * (β + 4))) := by rw [hmult_def]; ring
    have hReq :
        36 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 *
              M ^ 4
          = mult * (18 * M * β ^ 2 * μ₁) := by rw [hmult_def]; ring
    rw [hLeq, hReq]; exact hscaled
  exact le_of_sq_le_sq hL2_le hRt_nonneg

/-- Piece D of the Φ₄ mapping.  Constant `c_D = 10`.  Uses the squared middle
sample bound `M² ≥ μ₀·μ₁²·(N·R·(β·logN))²`. -/
private lemma piece_D_le
    (N R M mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef : ℝ)
    (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hmn_pos : 0 < mn)
    (hlog : 0 ≤ logN) (hβ : 2 < β)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hM_pos : 0 < M)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef)
    (hmlowD : M ^ 2 ≥ μ₀ * μ₁ ^ 2 * (N * R * (β * logN)) ^ 2) :
    (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          ((μ₀ * R / mn) *
            ((((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn))))))
      ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 10) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) := by
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hbl : 0 ≤ β * logN := by positivity
  have hs2 : 0 ≤ ((β + 2) * logN) / p := by positivity
  have hs4 : 0 ≤ ((β + 4) * logN) / p := by positivity
  set L := (Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          ((μ₀ * R / mn) *
            ((((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn)))))) with hL
  set Rt := ((Ctail * Real.sqrt Cenergy * Ccoef * 10) *
        Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)) with hRt
  have hL_nonneg : 0 ≤ L := by rw [hL]; positivity
  have hRt_nonneg : 0 ≤ Rt := by
    rw [hRt]
    have : 0 ≤ Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hL2 : L ^ 2 =
      2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 5 * R ^ 5 * β * logN ^ 5 * μ₀ ^ 4 * μ₁ ^ 2 *
        ((β + 2) ^ 2 * (β + 4) ^ 2) / M ^ 5 := by
    rw [hL]
    have e1 : Real.sqrt (2 * (β * logN)) ^ 2 = 2 * (β * logN) := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (Cenergy * p * N) ^ 2 = Cenergy * p * N := Real.sq_sqrt (by positivity)
    have e6 : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
    simp only [mul_pow]
    rw [e1, e2, e6, hp, hnn]
    field_simp
  have hRt2 : Rt ^ 2 =
      100 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 /
        M ^ 3 := by
    rw [hRt]
    have hrp : Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / M) ((3 : ℝ) / 2)
        = ((μ₀ * μ₁ * N * R * (β * logN)) / M) *
            Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) :=
      rpow_three_halves (by positivity)
    have e6 : Real.sqrt ((μ₀ * μ₁ * N * R * (β * logN)) / M) ^ 2
        = (μ₀ * μ₁ * N * R * (β * logN)) / M := Real.sq_sqrt (by positivity)
    have e7 : Real.sqrt Cenergy ^ 2 = Cenergy := Real.sq_sqrt (le_of_lt hCenergy)
    rw [hrp]
    simp only [mul_pow]
    rw [e6, e7]
    field_simp; ring
  have hkey : N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * ((β + 2) ^ 2 * (β + 4) ^ 2) ≤ 50 * M ^ 2 * β ^ 2 * μ₁ := by
    have hμ13 : (1 : ℝ) ≤ μ₁ ^ 3 := by nlinarith [hμ₁, sq_nonneg μ₁]
    have hfac : (0 : ℝ) ≤ 50 * β ^ 2 * μ₁ := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmlowD hfac
    have hbeta : (β + 2) ^ 2 * (β + 4) ^ 2 ≤ 50 * β ^ 4 := by nlinarith [hβ, sq_nonneg (β - 2)]
    have hbasefac : (0 : ℝ) ≤ N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ := by positivity
    have hbase : N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * ((β + 2) ^ 2 * (β + 4) ^ 2)
        ≤ N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * (50 * β ^ 4) :=
      mul_le_mul_of_nonneg_left hbeta hbasefac
    have hbig : (0 : ℝ) ≤ N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * (50 * β ^ 4) := by positivity
    have hmid : N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * (50 * β ^ 4)
        ≤ μ₁ ^ 3 * (N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * (50 * β ^ 4)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ13) hbig]
    have hend : μ₁ ^ 3 * (N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * (50 * β ^ 4)) ≤ 50 * M ^ 2 * β ^ 2 * μ₁ := by
      nlinarith [hstep]
    linarith [hbase, hmid, hend]
  have hL2_le : L ^ 2 ≤ Rt ^ 2 := by
    rw [hL2, hRt2, div_le_div_iff₀ (by positivity) (by positivity)]
    set mult : ℝ :=
      2 * (Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 2 * M ^ 3)
      with hmult_def
    have hmult : (0 : ℝ) ≤ mult := by rw [hmult_def]; positivity
    have hscaled := mul_le_mul_of_nonneg_left hkey hmult
    have hLeq :
        2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 5 * R ^ 5 * β * logN ^ 5 * μ₀ ^ 4 * μ₁ ^ 2 *
              ((β + 2) ^ 2 * (β + 4) ^ 2) * M ^ 3
          = mult * (N ^ 2 * R ^ 2 * logN ^ 2 * μ₀ * ((β + 2) ^ 2 * (β + 4) ^ 2)) := by
        rw [hmult_def]; ring
    have hReq :
        100 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 3 * β ^ 3 * logN ^ 3 * μ₀ ^ 3 * μ₁ ^ 3 *
              M ^ 5
          = mult * (50 * M ^ 2 * β ^ 2 * μ₁) := by rw [hmult_def]; ring
    rw [hLeq, hReq]; exact hscaled
  exact le_of_sq_le_sq hL2_le hRt_nonneg

/-- Conditional pointwise bound for the all-distinct decoupled contribution,
HONEST four-term version.  On the outer node-(iv) event and the honest pair
coefficient bound, the decoupled contribution has spectral norm `≤
Ctail·√Cenergy·Ccoef·27 · Φ₄`.  The all-distinct rep identity has NO scalar
prefactor, so the LHS is used directly (NO `nn/M` majorisation); the honest
four-term scale maps into `Φ₄`. -/
private lemma conditional_pointwise_bound
    {n₁ n₂ r m : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (β μ₀ μ₁ Ctail Cenergy Ccoef : ℝ)
    (q : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (hm : m ≤ n₁ * n₂) (hm_pos : 0 < m)
    (hβ : 2 < β) (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef)
    (hmax2 : 2 ≤ max n₁ n₂)
    (hqUpper : (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))))
    (hmlow2 : (m : ℝ) ≥ μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))))
    (hmlowD : (m : ℝ) ^ 2 ≥
        μ₀ * μ₁ ^ 2 *
          ((↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))) ^ 2)
    (Omega1 Omega2 Omega3 : Finset (Fin n₁ × Fin n₂))
    (hNodeIV :
      spectralNorm
          (centeredSamplingFluctuation Omega1
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) ≤
        Ctail * Real.sqrt (q : ℝ) *
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
          Real.sqrt
            (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) *
              entrySupNorm
                (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2))
    (hCoef :
      entrySupNorm
          (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
        Ccoef *
          (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                (Real.sqrt
                      (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                  (((β + 4) * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
            (((β + 2) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                (Real.sqrt
                      (((β + 4) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                  (((β + 4) * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))))) :
    spectralNorm
        (quadraticNeumannAllDistinctDecoupledContribution
          Omega1 Omega2 Omega3 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
      (Ctail * Real.sqrt Cenergy * Ccoef * 27) *
        Real.rpow
          ((μ₀ * μ₁ * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) ((3 : ℝ) / 2) := by
  classical
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mo : ℝ := (m : ℝ) with hMo
  set mn : ℝ := (↑(min n₁ n₂) : ℝ) with hmn
  set nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ) with hnn
  set logN : ℝ := Real.log N with hlogN
  set p : ℝ := Mo / nn with hp
  set cM := quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p with hcM
  -- basic positivity
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast (lt_of_lt_of_le hn₁ (Nat.le_max_left _ _))
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast (le_trans hn₁ (Nat.le_max_left _ _))
  have hR1 : 1 ≤ R := by rw [hR]; exact_mod_cast hr
  have hmn_pos : 0 < mn := by rw [hmn]; exact_mod_cast (lt_min hn₁ hn₂)
  have hMo_pos : 0 < Mo := by rw [hMo]; exact_mod_cast hm_pos
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hlog_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN1
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hnn_eq : nn = N * mn := by
    rw [hN, hmn, hnn]
    have := max_mul_min (n₁) (n₂)
    have hcast : ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
      exact_mod_cast this
    linarith [hcast]
  -- entrySup ≥ 0
  have hES_nonneg : 0 ≤ entrySupNorm cM := by
    rw [hcM]
    unfold entrySupNorm
    haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
    haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
    apply Real.iSup_nonneg
    intro i; apply Real.iSup_nonneg; intro j; exact abs_nonneg _
  -- Step 1: rep identity (NO scalar prefactor)
  have hrep :
      quadraticNeumannAllDistinctDecoupledContribution Omega1 Omega2 Omega3 S p =
        centeredSamplingFluctuation Omega1 p cM := by
    rw [hcM]
    exact
      quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
        Omega1 Omega2 Omega3 S p
  -- √EnergyBound = √(Cenergy·p·N)·entrySup
  have hsqrtEB :
      Real.sqrt (Cenergy * p * N * entrySupNorm cM ^ 2) =
        Real.sqrt (Cenergy * p * N) * entrySupNorm cM := by
    rw [show Cenergy * p * N * entrySupNorm cM ^ 2
        = (Cenergy * p * N) * entrySupNorm cM ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hES_nonneg]
  -- honest four-term scale in folded variables
  set fourTerm : ℝ :=
    Real.sqrt (((β + 2) * logN) / p) *
        (Real.sqrt (μ₀ * R / mn) *
          (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn)) +
            (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn)))) +
      (((β + 2) * logN) / p) *
        ((μ₀ * R / mn) *
          (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn)) +
            (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn)))) with hfourTerm
  have hCoef' : entrySupNorm cM ≤ Ccoef * fourTerm := hCoef
  -- node (iv) bound, √EB split
  have hNode' :
      spectralNorm (centeredSamplingFluctuation Omega1 p cM) ≤
        Ctail * Real.sqrt (q : ℝ) * p⁻¹ *
          (Real.sqrt (Cenergy * p * N) * entrySupNorm cM) := by
    have h := hNodeIV
    rw [hsqrtEB] at h
    exact h
  set sEB : ℝ := Real.sqrt (Cenergy * p * N) with hsEB
  have hsEB_nonneg : 0 ≤ sEB := by rw [hsEB]; exact Real.sqrt_nonneg _
  have hCtail_nonneg : 0 ≤ Ctail := le_of_lt hCtail
  have hpinv_nonneg : 0 ≤ p⁻¹ := by positivity
  have hqbound : Real.sqrt (q : ℝ) ≤ Real.sqrt (2 * (β * logN)) :=
    Real.sqrt_le_sqrt (by simpa [hlogN, mul_comm] using hqUpper)
  have hfourTerm_nonneg : 0 ≤ fourTerm := by rw [hfourTerm]; positivity
  -- Step 1': decoupled spectral ≤ node-(iv)-RHS with coefficient bound plugged in
  have hStep1 :
      spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution
            Omega1 Omega2 Omega3 S p) ≤
        Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * fourTerm)) := by
    rw [hrep]
    have hnodeES :
        Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * entrySupNorm cM) ≤
          Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * fourTerm)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hCoef' hsEB_nonneg
    exact le_trans (by rw [hsEB] at hNode' ⊢; exact hNode') hnodeES
  -- bound √q by √(2βlogN)
  have hStep2 :
      Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * fourTerm)) ≤
        Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * (sEB * (Ccoef * fourTerm)) := by
    have hrest_nonneg : 0 ≤ p⁻¹ * (sEB * (Ccoef * fourTerm)) := by positivity
    have hexp1 : Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * fourTerm))
        = Ctail * (Real.sqrt (q : ℝ) * (p⁻¹ * (sEB * (Ccoef * fourTerm)))) := by ring
    have hexp2 : Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * (sEB * (Ccoef * fourTerm))
        = Ctail * (Real.sqrt (2 * (β * logN)) * (p⁻¹ * (sEB * (Ccoef * fourTerm)))) := by ring
    rw [hexp1, hexp2]
    apply mul_le_mul_of_nonneg_left _ hCtail_nonneg
    exact mul_le_mul_of_nonneg_right hqbound hrest_nonneg
  -- expand into the four pieces
  set pref : ℝ := Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * sEB * Ccoef with hpref
  set Aterm : ℝ :=
    Real.sqrt (((β + 2) * logN) / p) *
      (Real.sqrt (μ₀ * R / mn) *
        (Real.sqrt (((β + 4) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn)))) with hAterm
  set Bterm : ℝ :=
    Real.sqrt (((β + 2) * logN) / p) *
      (Real.sqrt (μ₀ * R / mn) *
        ((((β + 4) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn)))) with hBterm
  set Cterm : ℝ :=
    (((β + 2) * logN) / p) *
      ((μ₀ * R / mn) *
        (Real.sqrt (((β + 4) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn)))) with hCterm
  set Dterm : ℝ :=
    (((β + 2) * logN) / p) *
      ((μ₀ * R / mn) *
        ((((β + 4) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn)))) with hDterm
  have hExpand :
      Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * (sEB * (Ccoef * fourTerm)) =
        pref * Aterm + pref * Bterm + pref * Cterm + pref * Dterm := by
    rw [hpref, hAterm, hBterm, hCterm, hDterm, hfourTerm]; ring
  -- the abbreviated Φ₄
  set Φ₄ : ℝ := Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mo) ((3 : ℝ) / 2) with hΦ₄
  -- each pref·Xterm = the piece LHS
  have hPA := piece_A_le N R Mo mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef
    hN1 hR1 hmn_pos hlog_nonneg hβ hμ₀ hμ₁ hMo_pos hnn_eq hp hCtail hCenergy hCcoef
  have hPB := piece_B_le N R Mo mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef
    hN1 hR1 hmn_pos hlog_nonneg hβ hμ₀ hμ₁ hMo_pos hnn_eq hp hCtail hCenergy hCcoef hmlow2
  have hPC := piece_C_le N R Mo mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef
    hN1 hR1 hmn_pos hlog_nonneg hβ hμ₀ hμ₁ hMo_pos hnn_eq hp hCtail hCenergy hCcoef hmlow2
  have hmlowD' : Mo ^ 2 ≥ μ₀ * μ₁ ^ 2 * (N * R * (β * logN)) ^ 2 := by
    rw [hMo, hN, hR, hlogN, hN]; exact hmlowD
  have hPD := piece_D_le N R Mo mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef
    hN1 hR1 hmn_pos hlog_nonneg hβ hμ₀ hμ₁ hMo_pos hnn_eq hp hCtail hCenergy hCcoef hmlowD'
  rw [← hsEB] at hPA hPB hPC hPD
  -- pref·Xterm equals the LHS of piece_X_le
  have hpAeq : pref * Aterm =
      Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (Real.sqrt (μ₀ * R / mn) *
            (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn))))) := by
    rw [hpref, hAterm, hsEB]
  have hpBeq : pref * Bterm =
      Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (Real.sqrt (μ₀ * R / mn) *
            ((((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn))))) := by
    rw [hpref, hBterm, hsEB]
  have hpCeq : pref * Cterm =
      Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          ((μ₀ * R / mn) *
            (Real.sqrt (((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn))))) := by
    rw [hpref, hCterm, hsEB]
  have hpDeq : pref * Dterm =
      Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          ((μ₀ * R / mn) *
            ((((β + 4) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn))))) := by
    rw [hpref, hDterm, hsEB]
  -- assemble
  have hΦ₄_nonneg : 0 ≤ Φ₄ := by rw [hΦ₄]; exact Real.rpow_nonneg (by positivity) _
  have hsum :
      pref * Aterm + pref * Bterm + pref * Cterm + pref * Dterm ≤
        (Ctail * Real.sqrt Cenergy * Ccoef * 27) * Φ₄ := by
    rw [hpAeq, hpBeq, hpCeq, hpDeq]
    have hΦ₄def : Φ₄ = Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mo) ((3 : ℝ) / 2) := hΦ₄
    rw [hΦ₄def]
    calc _ ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 4) *
              Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mo) ((3 : ℝ) / 2) +
            (Ctail * Real.sqrt Cenergy * Ccoef * 7) *
              Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mo) ((3 : ℝ) / 2) +
            (Ctail * Real.sqrt Cenergy * Ccoef * 6) *
              Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mo) ((3 : ℝ) / 2) +
            (Ctail * Real.sqrt Cenergy * Ccoef * 10) *
              Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mo) ((3 : ℝ) / 2) := by
          exact add_le_add (add_le_add (add_le_add hPA hPB) hPC) hPD
      _ = (Ctail * Real.sqrt Cenergy * Ccoef * 27) *
              Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mo) ((3 : ℝ) / 2) := by ring
  have hfinal :
      spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution
            Omega1 Omega2 Omega3 S p) ≤
        (Ctail * Real.sqrt Cenergy * Ccoef * 27) * Φ₄ :=
    le_trans hStep1 (le_trans hStep2 (le_trans (le_of_eq hExpand) hsum))
  simpa only [hp, hN, hR, hMo, hmn, hnn, hlogN, hΦ₄] using hfinal

end MatrixCompletion

/-- Child A (honest four-term scale). -/
theorem solution :
    ∃ Cdec cdec : ℝ, 0 < Cdec ∧ 0 < cdec ∧
      ∀ C' : ℝ, Cdec ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cdec *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) := by
  classical
  obtain ⟨Ctail, Cenergy, hCtail, hCenergy, hNodeEvent⟩ :=
    centered_sampling_spectral_event_from_a0_energy_moment
  obtain ⟨Ccoef, ccoef, hCcoef, hccoef, hCoefEvent⟩ :=
    quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim
  refine ⟨max 1 (Ctail * Real.sqrt Cenergy * Ccoef * 27), 1 + ccoef,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  set Cdec : ℝ := max 1 (Ctail * Real.sqrt Cenergy * Ccoef * 27) with hCdec
  have hC'_one : (1 : ℝ) ≤ C' := le_trans (le_max_left _ _) hC'
  have h27le : Ctail * Real.sqrt Cenergy * Ccoef * 27 ≤ Cdec := le_max_right _ _
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hNnat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left _ _)
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hNnat
  have hlog_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN1
  have hμ₀nn : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁nn : (0 : ℝ) ≤ μ₁ := le_trans zero_le_one hμ₁
  have hβnn : (0 : ℝ) ≤ β := le_of_lt (lt_trans (by norm_num) hβ)
  have hRnn : (0 : ℝ) ≤ R := by rw [hR]; positivity
  have hMobsnn : (0 : ℝ) ≤ Mobs := by rw [hMobs]; positivity
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  -- Φ and its four nonneg summands
  set Φ₁ : ℝ := (μ₀ ^ 2 * μ₁) * Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2
    with hΦ₁
  set Φ₂ : ℝ := μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 with hΦ₂
  set Φ₃ : ℝ := Real.sqrt (β * logN) * Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)
    with hΦ₃
  set Φ₄ : ℝ := Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) with hΦ₄
  set Φ : ℝ := Φ₁ + Φ₂ + Φ₃ + Φ₄ with hΦ
  have hΦ₁nn : 0 ≤ Φ₁ := by rw [hΦ₁]; positivity
  have hΦ₂nn : 0 ≤ Φ₂ := by rw [hΦ₂]; positivity
  have hΦ₃nn : 0 ≤ Φ₃ := by
    rw [hΦ₃]
    have : 0 ≤ Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hΦ₄nn : 0 ≤ Φ₄ := by rw [hΦ₄]; exact Real.rpow_nonneg (by positivity) _
  have hΦnn : 0 ≤ Φ := by rw [hΦ]; linarith
  -- reduce the goal's let-block to `spectralNorm ≤ Cdec * Φ`
  show bernoulliTripleEventProb p
      (fun Omega1 Omega2 Omega3 =>
        spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution
            Omega1 Omega2 Omega3 S p) ≤ Cdec * Φ) ≥
    1 - (1 + ccoef) * Real.rpow (↑(max n₁ n₂)) (-β)
  -- edge: max n₁ n₂ < 2 ⇒ decoupled ≡ 0 ⇒ event always holds
  by_cases hmax2 : 2 ≤ max n₁ n₂
  · -- main branch
    have hmLower' : (m : ℝ) ≥ C' *
        max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
          (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) *
          N * R * (β * logN) := by
      simpa [hN, hR, hlogN, mul_assoc] using hmLower
    have hR1nat : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast hr
    -- (a) m ≥ β·N·logN
    have hSampleFixed : (m : ℝ) ≥ β * N * logN := by
      have hprod : β * N * logN ≤ C' *
          max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) * N * R * (β * logN) := by
        have hbase : β * N * logN = 1 * 1 * N * 1 * (β * logN) := by ring
        rw [hbase]
        have hmaxge : (1 : ℝ) ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := by
          have hμ₁sq : (1 : ℝ) ≤ μ₁ ^ 2 := by nlinarith [hμ₁]
          exact le_trans hμ₁sq (le_trans (le_max_left _ _) (le_max_left _ _))
        have hRge : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast hr
        gcongr
      linarith [hmLower']
    have hSampleFixed' : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
      have : β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) = β * N * logN := by
        rw [hN, hlogN, hN]
      rw [this]; exact hSampleFixed
    -- (b) m ≥ µ₁²·N·r·βlogN
    have hmlow2 : (m : ℝ) ≥ μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) := by
      have hprod : μ₁ ^ 2 * N * R * (β * logN) ≤ C' *
          max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) * N * R * (β * logN) := by
        have hμ₁sqle : μ₁ ^ 2 ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        have hNRl_nonneg : 0 ≤ N * R * (β * logN) := by rw [hR]; positivity
        calc μ₁ ^ 2 * N * R * (β * logN)
            = μ₁ ^ 2 * (N * R * (β * logN)) := by ring
          _ ≤ (C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))) * (N * R * (β * logN)) := by
              apply mul_le_mul_of_nonneg_right _ hNRl_nonneg
              calc μ₁ ^ 2 ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                    (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := hμ₁sqle
                _ = 1 * _ := (one_mul _).symm
                _ ≤ C' * _ := by
                    apply mul_le_mul_of_nonneg_right hC'_one
                    exact le_trans (sq_nonneg μ₁) hμ₁sqle
          _ = _ := by ring
      calc μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))
          = μ₁ ^ 2 * N * R * (β * logN) := by rw [hN, hR, hlogN, hN]
        _ ≤ _ := hprod
        _ ≤ (m : ℝ) := by simpa [hN, hR, hlogN, mul_assoc] using hmLower'
    -- (c) m ≥ (√µ₀·µ₁)·N·r·βlogN  ⇒ squared:  m² ≥ µ₀·µ₁²·(N·R·βlogN)²
    have hmlow_mid : (m : ℝ) ≥ (Real.sqrt μ₀ * μ₁) * N * R * (β * logN) := by
      have hprod : (Real.sqrt μ₀ * μ₁) * N * R * (β * logN) ≤ C' *
          max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) * N * R * (β * logN) := by
        have hmidle : (Real.sqrt μ₀ * μ₁) ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        have hNRl_nonneg : 0 ≤ N * R * (β * logN) := by rw [hR]; positivity
        have hmid_nonneg : 0 ≤ Real.sqrt μ₀ * μ₁ := by positivity
        calc (Real.sqrt μ₀ * μ₁) * N * R * (β * logN)
            = (Real.sqrt μ₀ * μ₁) * (N * R * (β * logN)) := by ring
          _ ≤ (C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))) * (N * R * (β * logN)) := by
              apply mul_le_mul_of_nonneg_right _ hNRl_nonneg
              calc (Real.sqrt μ₀ * μ₁) ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                    (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := hmidle
                _ = 1 * _ := (one_mul _).symm
                _ ≤ C' * _ := by
                    apply mul_le_mul_of_nonneg_right hC'_one
                    exact le_trans hmid_nonneg hmidle
          _ = _ := by ring
      calc (Real.sqrt μ₀ * μ₁) * N * R * (β * logN)
          ≤ _ := hprod
        _ ≤ (m : ℝ) := by simpa [hN, hR, hlogN, mul_assoc] using hmLower'
    have hmlowD : (m : ℝ) ^ 2 ≥
        μ₀ * μ₁ ^ 2 *
          ((↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))) ^ 2 := by
      have hmid_nonneg : 0 ≤ (Real.sqrt μ₀ * μ₁) * N * R * (β * logN) := by
        have : 0 ≤ Real.sqrt μ₀ * μ₁ := by positivity
        rw [hR]; positivity
      have hsq := mul_le_mul hmlow_mid hmlow_mid hmid_nonneg hMobsnn
      -- hsq : ((√µ₀·µ₁)·N·R·βlogN)² ≤ m²
      have hexp : ((Real.sqrt μ₀ * μ₁) * N * R * (β * logN)) *
          ((Real.sqrt μ₀ * μ₁) * N * R * (β * logN)) =
          μ₀ * μ₁ ^ 2 * (N * R * (β * logN)) ^ 2 := by
        have hsqμ₀ : Real.sqrt μ₀ * Real.sqrt μ₀ = μ₀ := Real.mul_self_sqrt hμ₀nn
        linear_combination (μ₁ ^ 2 * (N * R * (β * logN)) ^ 2) * hsqμ₀
      rw [hexp] at hsq
      have : μ₀ * μ₁ ^ 2 * (N * R * (β * logN)) ^ 2
          = μ₀ * μ₁ ^ 2 * ((↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))) ^ 2 := by
        rw [hN, hR, hlogN, hN]
      rw [this] at hsq
      have hmm : (Mobs) * (Mobs) = (m : ℝ) ^ 2 := by rw [hMobs]; ring
      rw [hmm] at hsq
      exact hsq
    have hm_pos : 0 < m := by
      by_contra h
      push_neg at h
      interval_cases m
      · simp at hSampleFixed
        have : 0 < β * N * logN := by
          have hlogpos : 0 < logN := by
            rw [hlogN]; exact Real.log_pos (by rw [hN]; exact_mod_cast hmax2)
          positivity
        linarith [hSampleFixed]
    -- pair (marginal) event over (Ω2,Ω3) for the coefficient bound
    have hMarg := hCoefEvent β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
    -- triple lift
    have htriple :=
      bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
        (n₁ := n₁) (n₂ := n₂) p ccoef 1 (Real.rpow (↑(max n₁ n₂)) (-β))
        (fun Omega2 Omega3 =>
          QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
            (Ccoef *
              (Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                    (Real.sqrt (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
                (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                    (Real.sqrt (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))))))
        (fun Omega1 Omega2 Omega3 =>
          spectralNorm
            (quadraticNeumannAllDistinctDecoupledContribution
              Omega1 Omega2 Omega3 S p) ≤ Cdec * Φ)
        hp0 hp1
        (by
          have : (0 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) (-β) := Real.rpow_nonneg (by positivity) _
          positivity) ?_ ?_
    · exact htriple
    · -- pair marginal ≥ 1 - cPair·scale = 1 - ccoef·scale
      simpa [hp] using hMarg
    · -- conditional over Ω1
      intro Omega2 Omega3 hMargGood
      have hNode := hNodeEvent β hβ n₁ n₂ m
        (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p)
        hn₁ hn₂ hm hSampleFixed' hmax2
      obtain ⟨q, hq1, hqLog, hqUpper, hNodeProb⟩ := hNode
      have hCoefBound :
          entrySupNorm
              (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p) ≤
            Ccoef *
              (Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                    (Real.sqrt (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
                (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                    (Real.sqrt (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) := by
        exact
          quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
            Omega2 Omega3 S p _ hn₁ hn₂ hMargGood
      refine le_trans hNodeProb ?_
      apply bernoulli_event_probability_mono p _ _ hp0 hp1
      intro Omega1 hΩ1
      have hNodeIV := hΩ1
      unfold CenteredSamplingSpectralBound at hNodeIV
      have hcond :=
        conditional_pointwise_bound S β μ₀ μ₁ Ctail Cenergy Ccoef q
          hn₁ hn₂ hr hm hm_pos hβ hμ₀ hμ₁ hCtail hCenergy hCcoef hmax2
          hqUpper hmlow2 hmlowD Omega1 Omega2 Omega3 hNodeIV hCoefBound
      refine le_trans hcond ?_
      have hΦ₄eq :
          Real.rpow
              ((μ₀ * μ₁ * (↑(max n₁ n₂)) * (r : ℝ) *
                  (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) ((3 : ℝ) / 2) = Φ₄ := by
        rw [hΦ₄, hN, hR, hMobs, hlogN, hN]
      rw [hΦ₄eq]
      calc (Ctail * Real.sqrt Cenergy * Ccoef * 27) * Φ₄
          ≤ Cdec * Φ₄ := mul_le_mul_of_nonneg_right h27le hΦ₄nn
        _ ≤ Cdec * Φ := by
            apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (le_max_left _ _))
            rw [hΦ]; linarith
  · -- edge: max n₁ n₂ = 1 ⇒ decoupled ≡ 0
    push_neg at hmax2
    have hzero : ∀ (Ω1 Ω2 Ω3 : Finset (Fin n₁ × Fin n₂)),
        quadraticNeumannAllDistinctDecoupledContribution Ω1 Ω2 Ω3 S p = 0 := by
      intro Ω1 Ω2 Ω3
      have hn1 : n₁ ≤ 1 := le_trans (Nat.le_max_left n₁ n₂) (Nat.lt_succ_iff.mp hmax2)
      have hn2 : n₂ ≤ 1 := le_trans (Nat.le_max_right n₁ n₂) (Nat.lt_succ_iff.mp hmax2)
      haveI : Subsingleton (Fin n₁ × Fin n₂) := by
        constructor; intro a b
        have : Subsingleton (Fin n₁) := ⟨fun x y => Fin.ext (by omega)⟩
        have : Subsingleton (Fin n₂) := ⟨fun x y => Fin.ext (by omega)⟩
        exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      rw [quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation]
      have hXzero : quadraticAllDistinctOuterCoefficientMatrix Ω2 Ω3 S p = 0 := by
        funext i j
        unfold quadraticAllDistinctOuterCoefficientMatrix quadraticAllDistinctMiddleCoefficient
        refine mul_eq_zero.mpr (Or.inr ?_)
        apply Finset.sum_eq_zero; intro w2 _
        have : w2 = (i, j) := Subsingleton.elim _ _
        simp [this]
      rw [hXzero]
      have hsp : samplingProjection Ω1 (0 : RealMatrix n₁ n₂) = 0 := by
        funext i j; simp [samplingProjection]
      show p⁻¹ • (samplingProjection Ω1 (0 : RealMatrix n₁ n₂)
        - p • (0 : RealMatrix n₁ n₂)) = 0
      rw [hsp, smul_zero, sub_zero, smul_zero]
    have hspec0 : ∀ (Ω1 Ω2 Ω3 : Finset (Fin n₁ × Fin n₂)),
        spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution Ω1 Ω2 Ω3 S p) = 0 := by
      intro Ω1 Ω2 Ω3
      rw [hzero]; unfold spectralNorm; simp
    have hall :
        bernoulliTripleEventProb p
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S p) ≤ Cdec * Φ) = 1 := by
      unfold bernoulliTripleEventProb
      have hev : ∀ Ω1 Ω2 Ω3, (spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution Ω1 Ω2 Ω3 S p) ≤
            Cdec * Φ) := by
        intro Ω1 Ω2 Ω3; rw [hspec0]
        exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hΦnn
      simp only [hev, if_true, mul_one]
      have hone : (∑ Omega : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega) = 1 := bernoulliObservationWeight_sum_eq_one
      have hstep : ∀ x x_1 : Finset (Fin n₁ × Fin n₂),
          (∑ x_2 : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p x * bernoulliObservationWeight p x_1 *
              bernoulliObservationWeight p x_2) =
            bernoulliObservationWeight p x * bernoulliObservationWeight p x_1 := by
        intro x x_1
        rw [← Finset.mul_sum, hone, mul_one]
      simp_rw [hstep]
      have hstep2 : ∀ x : Finset (Fin n₁ × Fin n₂),
          (∑ x_1 : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p x * bernoulliObservationWeight p x_1) =
            bernoulliObservationWeight p x := by
        intro x
        rw [← Finset.mul_sum, hone, mul_one]
      simp_rw [hstep2]
      exact hone
    rw [hall]
    have : (0 : ℝ) ≤ (1 + ccoef) * Real.rpow (↑(max n₁ n₂)) (-β) := by
      have : 0 ≤ Real.rpow (↑(max n₁ n₂)) (-β) := Real.rpow_nonneg (by positivity) _
      positivity
    linarith
