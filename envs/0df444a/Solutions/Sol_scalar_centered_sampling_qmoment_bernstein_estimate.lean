-- Prove2me | solution 1 for scalar_centered_sampling_qmoment_bernstein_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T23:48:56.250273+00:00
-- url     : https://prove2.me/submissions/6de2815a-d3a1-4bb4-a454-6ae919754d29

import Theorems.Thm_scalar_centered_sampling_qnorm_rosenthal_estimate
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

namespace Prove75459

variable {n₁ n₂ : ℕ}

/-- `e^{-q} ≤ n^{-β}` whenever `q ≥ β·log n` and `n ≥ 1`. -/
theorem exp_neg_le_rpow_neg (n β : ℝ) (hn : 1 ≤ n) (q : ℝ)
    (hq : β * Real.log n ≤ q) : Real.exp (-q) ≤ Real.rpow n (-β) := by
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have hr : Real.rpow n (-β) = Real.exp (Real.log n * (-β)) := Real.rpow_def_of_pos hnpos _
  rw [hr, Real.exp_le_exp]; nlinarith [hq]

/-- `√(q/p) ≤ (q/bl)·√(bl/p)` for `q ≥ bl > 0`, `p > 0`. -/
theorem sqrt_ratio_le (p bl q : ℝ) (hp : 0 < p) (hbl : 0 < bl) (hq : bl ≤ q) :
    Real.sqrt (q/p) ≤ (q/bl) * Real.sqrt (bl/p) := by
  have hqpos0 : 0 < q := lt_of_lt_of_le hbl hq
  rw [show (q/bl) * Real.sqrt (bl/p) = Real.sqrt ((q/bl)^2 * (bl/p)) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  rw [show (q/bl)^2 * (bl/p) = q^2 / (bl * p) by field_simp]
  rw [div_le_div_iff₀ hp (by positivity)]
  have hqpos : 0 < q := lt_of_lt_of_le hbl hq
  nlinarith [hq, hbl, hp, hqpos, mul_le_mul_of_nonneg_right hq (le_of_lt hqpos)]

/-- The inner factor comparison `J(q) ≤ (q/bl)·M`. -/
theorem inner_ratio_le (p bl q F E : ℝ) (hp : 0 < p) (hbl : 0 < bl) (hq : bl ≤ q)
    (hF : 0 ≤ F) (hE : 0 ≤ E) :
    Real.sqrt (q/p) * F + (q/p) * E ≤ (q/bl) * (Real.sqrt (bl/p) * F + (bl/p) * E) := by
  have h1 : Real.sqrt (q/p) * F ≤ (q/bl) * (Real.sqrt (bl/p) * F) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (sqrt_ratio_le p bl q hp hbl hq) hF
  have h2 : (q/p) * E ≤ (q/bl) * ((bl/p) * E) := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hE
    rw [div_mul_div_comm, div_le_div_iff₀ hp (by positivity)]
    have hqpos : 0 < q := lt_of_lt_of_le hbl hq
    nlinarith [hq, hbl, hp, hqpos]
  calc Real.sqrt (q/p) * F + (q/p) * E
      ≤ (q/bl) * (Real.sqrt (bl/p) * F) + (q/bl) * ((bl/p) * E) := add_le_add h1 h2
    _ = (q/bl) * (Real.sqrt (bl/p) * F + (bl/p) * E) := by ring

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The Bernoulli observation weights sum to 1. -/
theorem weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const, Finset.card_compl]

/-- Degeneracy at `p = 0`: the fluctuation is identically `0`, so the moment vanishes. -/
theorem moment_zero_of_p_zero (q : ℕ) (hq : 1 ≤ q)
    (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hCoeff : ∀ Omega : Finset (Fin n₁ × Fin n₂),
       Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (0:ℝ) B)) :
    bernoulliExpectation (0:ℝ) (fun Omega => |Coeff Omega| ^ q) = 0 := by
  have hzero : ∀ Omega : Finset (Fin n₁ × Fin n₂), Coeff Omega = 0 := by
    intro Omega; rw [hCoeff]
    unfold matrixEntrySum centeredSamplingFluctuation
    simp [inv_zero]
  unfold bernoulliExpectation
  refine Finset.sum_eq_zero (fun Omega _ => ?_)
  simp only [hzero, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]

/-- Degeneracy at `n₁ = n₂ = 1`, `p = 1`: the fluctuation vanishes on the full set
and the empty set carries weight `0`, so the moment vanishes. -/
theorem moment_zero_of_n_one (q : ℕ) (hq : 1 ≤ q)
    (Coeff : Finset (Fin 1 × Fin 1) → ℝ) (B : Matrix (Fin 1) (Fin 1) ℝ)
    (hCoeff : ∀ Omega : Finset (Fin 1 × Fin 1),
       Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (1:ℝ) B)) :
    bernoulliExpectation (1:ℝ) (fun Omega => |Coeff Omega| ^ q) = 0 := by
  unfold bernoulliExpectation
  refine Finset.sum_eq_zero (fun Omega _ => ?_)
  simp only []
  have hsingle : ∀ x : Fin 1 × Fin 1, x = (0,0) := by
    intro x; obtain ⟨a, b⟩ := x; fin_cases a <;> fin_cases b <;> rfl
  by_cases hmem : (0,0) ∈ Omega
  · have huniv : Omega = Finset.univ :=
      Finset.eq_univ_of_forall (fun x => by rw [hsingle x]; exact hmem)
    have hC0 : Coeff Omega = 0 := by
      rw [hCoeff]
      unfold matrixEntrySum
      refine Finset.sum_eq_zero (fun w _ => ?_)
      show (1:ℝ)⁻¹ * ((samplingProjection Omega B) w.1 w.2 - (1:ℝ) * B w.1 w.2) = 0
      simp [samplingProjection, huniv]
    simp only [hC0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
  · have hempty : Omega = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩; rw [hsingle x] at hx; exact hmem hx
    have hw : bernoulliObservationWeight (1:ℝ) Omega = 0 := by
      rw [hempty]; unfold bernoulliObservationWeight; simp
    rw [hw, zero_mul]

end Prove75459

open Prove75459 in
/-- `scalar_centered_sampling_qmoment_bernstein_estimate` (75459b07) as a reduction
onto the Rosenthal/Bernstein q-norm core
`scalar_centered_sampling_qnorm_rosenthal_estimate`. See the q-norm node for the
sourced statement (Rosenthal 1970; Boucheron–Lugosi–Massart Ch. 15;
Candès–Recht arXiv:0805.4471 §6).

Choose `q = ⌈β·log(max n₁ n₂)⌉`. For `max n₁ n₂ ≥ 2` and `p > 0`,
`bl := β·log n > β·log 2 > 1` (as `β > 2`), so `bl ≤ q ≤ 2·bl` and the core's inner
factor `J(q) ≤ (q/bl)·M ≤ 2·M`. With `Cbern = 2·e·C`, `cbern = 1`,
`E|Coeff|^q ≤ (C·J(q))^q ≤ (2C·M)^q ≤ (Cbern·M)^q·e^{-q} ≤ (Cbern·M)^q·n^{-β}`.
The degenerate cases `p = 0` (`m = 0`) and `n₁ = n₂ = 1` (`p ∈ {0,1}`) give
`E|Coeff|^q = 0 = RHS`. -/
theorem solution :
    ∃ Cbern cbern : ℝ, 0 < Cbern ∧ 0 < cbern ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∃ q : ℕ, 1 ≤ q ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (Cbern *
                (Real.sqrt
                    ((β * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((β * Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q *
              (cbern * Real.rpow (↑(max n₁ n₂)) (-β)) := by
  obtain ⟨C, hCpos, hcore⟩ := scalar_centered_sampling_qnorm_rosenthal_estimate
  refine ⟨2 * Real.exp 1 * C, 1, by positivity, one_pos, ?_⟩
  intro β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set nn : ℝ := (↑(max n₁ n₂) : ℝ) with hnn
  set bl : ℝ := β * Real.log nn with hbl
  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hmle
    push_cast at this; linarith
  have hmaxpos : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hnn1 : 1 ≤ nn := by rw [hnn]; exact_mod_cast hmaxpos
  have hnnpos : 0 < nn := lt_of_lt_of_le one_pos hnn1
  have hentrySN_nn : 0 ≤ entrySupNorm B :=
    Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hfrobN_nn : 0 ≤ frobeniusNorm B := by unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hE_nn : 0 ≤ entryScale := le_trans hentrySN_nn hentry
  have hF_nn : 0 ≤ frobScale := le_trans hfrobN_nn hfrob
  -- failProb ≥ 0
  have hrpow_nn : 0 ≤ Real.rpow nn (-β) := le_of_lt (Real.rpow_pos_of_pos hnnpos _)
  -- Degenerate case p = 0
  by_cases hpz : p = 0
  · refine ⟨1, le_refl 1, ?_⟩
    have hcoeff0 : ∀ Omega : Finset (Fin n₁ × Fin n₂),
        Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (0:ℝ) B) := by
      intro Omega; rw [hCoeff, hpz]
    have hmom0 := moment_zero_of_p_zero (n₁ := n₁) (n₂ := n₂) 1 (le_refl 1) Coeff B hcoeff0
    rw [hpz, hmom0]
    -- RHS = 0 since bl/0 = 0 ⇒ inner = 0
    simp only [div_zero, Real.sqrt_zero, zero_mul, add_zero, mul_zero, pow_one, le_refl]
  · -- p > 0
    have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
    by_cases hmax1 : max n₁ n₂ = 1
    · -- n₁ = n₂ = 1, p ∈ {0,1}, and p > 0 forces p = 1
      have hn1e : n₁ = 1 := by omega
      have hn2e : n₂ = 1 := by omega
      subst hn1e; subst hn2e
      -- p = m / 1 = m, and m ≤ 1, m > 0 (else p = 0), so m = 1, p = 1
      have hpm : p = (m : ℝ) := by rw [hp]; norm_num
      have hmpos : 0 < m := by
        by_contra h; push_neg at h; interval_cases m; simp [hpm] at hppos
      have hm1 : m = 1 := by omega
      have hpeq1 : p = 1 := by rw [hpm, hm1]; norm_num
      refine ⟨1, le_refl 1, ?_⟩
      have hcoeff1 : ∀ Omega : Finset (Fin 1 × Fin 1),
          Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (1:ℝ) B) := by
        intro Omega; rw [hCoeff, hpeq1]
      have hmom0 := moment_zero_of_n_one 1 (le_refl 1) Coeff B hcoeff1
      have hbl0 : bl = 0 := by
        rw [hbl, hnn]; norm_num
      rw [hpeq1, hmom0, hbl0]
      simp only [zero_div, Real.sqrt_zero, zero_mul, add_zero, mul_zero, pow_one, le_refl]
    · -- main case: max n₁ n₂ ≥ 2, p > 0
      have hmax2 : 2 ≤ max n₁ n₂ := by omega
      have hnn2 : 2 ≤ nn := by rw [hnn]; exact_mod_cast hmax2
      have hlog2 : Real.log 2 ≤ Real.log nn := Real.log_le_log (by norm_num) hnn2
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hblpos : 0 < bl := by
        rw [hbl]; exact mul_pos (by linarith) (lt_of_lt_of_le hlog2pos hlog2)
      have hbl1 : 1 < bl := by
        rw [hbl]
        have hstep : (2:ℝ) * Real.log 2 ≤ β * Real.log nn := by
          apply le_trans (le_of_lt (mul_lt_mul_of_pos_right hβ hlog2pos))
          exact mul_le_mul_of_nonneg_left hlog2 (by linarith)
        nlinarith [Real.log_two_gt_d9, hstep, hlog2pos]
      -- choose q = ⌈bl⌉
      set q : ℕ := ⌈bl⌉₊ with hqdef
      have hqge : bl ≤ (q : ℝ) := Nat.le_ceil bl
      have hqle : (q : ℝ) ≤ bl + 1 := by
        rw [hqdef]; exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt hblpos))
      have hq1 : 1 ≤ q := by
        rw [hqdef]; exact Nat.one_le_ceil_iff.mpr hblpos
      have hq2bl : (q : ℝ) ≤ 2 * bl := by nlinarith [hqge, hqle, hbl1]
      have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
      refine ⟨q, hq1, ?_⟩
      -- the core bound
      have hc := hcore n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob q hq1
      rw [← hp] at hc
      -- abbreviations for inner factors
      set M : ℝ := Real.sqrt (bl/p) * frobScale + (bl/p) * entryScale with hM
      set J : ℝ := Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale with hJ
      -- hc : bernoulliExpectation p (|Coeff|^q) ≤ (C * J)^q
      -- step 1: J ≤ (q/bl) * M ≤ 2 * M
      have hJM : J ≤ (q/bl) * M := by
        rw [hJ, hM]; exact inner_ratio_le p bl q frobScale entryScale hppos hblpos hqge hF_nn hE_nn
      have hMnn : 0 ≤ M := by
        rw [hM]; apply add_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hF_nn
        · exact mul_nonneg (by positivity) hE_nn
      have hqblle2 : (q:ℝ)/bl ≤ 2 := by rw [div_le_iff₀ hblpos]; linarith [hq2bl]
      have hJ2M : J ≤ 2 * M := by
        refine le_trans hJM ?_
        have := mul_le_mul_of_nonneg_right hqblle2 hMnn
        linarith [this]
      have hJnn : 0 ≤ J := by
        rw [hJ]; apply add_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hF_nn
        · exact mul_nonneg (by positivity) hE_nn
      -- step 2: (C*J)^q ≤ (C*(2*M))^q = (2*C*M)^q
      have hstep2 : (C * J)^q ≤ (2 * C * M)^q := by
        apply pow_le_pow_left₀ (by positivity)
        calc C * J ≤ C * (2 * M) := by
              exact mul_le_mul_of_nonneg_left hJ2M (le_of_lt hCpos)
          _ = 2 * C * M := by ring
      -- step 3: (2*C*M)^q ≤ (Cbern*M)^q * n^{-β}, Cbern = 2*e*C
      -- (Cbern*M)^q * n^{-β} = (2*e*C*M)^q * n^{-β} = (2*C*M)^q * e^q * n^{-β}
      have hexp : Real.exp (-(q:ℝ)) ≤ Real.rpow nn (-β) :=
        exp_neg_le_rpow_neg nn β hnn1 q (le_trans hqge (le_refl _))
      have hexpq_pos : 0 < Real.exp 1 ^ q := by positivity
      have h2CM_nn : 0 ≤ (2 * C * M)^q := by positivity
      have hfac : 1 ≤ (Real.exp 1)^q * Real.rpow nn (-β) := by
        have hee : (Real.exp 1)^q = Real.exp (q:ℝ) := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [hee]
        calc (1:ℝ) = Real.exp (q:ℝ) * Real.exp (-(q:ℝ)) := by
              rw [← Real.exp_add]; simp
          _ ≤ Real.exp (q:ℝ) * Real.rpow nn (-β) :=
              mul_le_mul_of_nonneg_left hexp (le_of_lt (Real.exp_pos _))
      have hstep3 : (2 * C * M)^q ≤ (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β)) := by
        have hbase : (2 * Real.exp 1 * C * M)^q = (2 * C * M)^q * (Real.exp 1)^q := by
          rw [← mul_pow]; congr 1; ring
        have hrw : (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β))
            = (2 * C * M)^q * ((Real.exp 1)^q * Real.rpow nn (-β)) := by
          rw [hbase, one_mul, mul_assoc]
        rw [hrw]
        exact le_mul_of_one_le_right h2CM_nn hfac
      -- combine
      calc bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q)
          ≤ (C * J)^q := hc
        _ ≤ (2 * C * M)^q := hstep2
        _ ≤ (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β)) := hstep3
