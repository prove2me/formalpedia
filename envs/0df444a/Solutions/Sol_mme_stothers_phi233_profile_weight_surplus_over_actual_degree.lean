-- Prove2me | solution 1 for mme_stothers_phi233_profile_weight_surplus_over_actual_degree
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T02:36:12.063717+00:00
-- url     : https://prove2.me/submissions/bdd5ecd9-e234-4606-be35-5f074724e481

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_q6_EHL_optimizer_regime
import Theorems.Thm_mme_stothers_phi233_positive_critical_profile_exists
import Theorems.Thm_mme_stothers_phi233_log_stationarity_of_critical_product
import Theorems.Thm_mme_stothers_phi233_asymptotic_completion_bridge
import Theorems.Thm_mme_stothers_phi233_exact_profile_nonempty
import Theorems.Thm_mme_stothers_phi233_exact_star_factorization
import Theorems.Thm_mme_stothers_phi233_cyclic_star_ratio
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities

open Real
open BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false

theorem phi233_binary_optimizer_log
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.binEntropy (x / (x + y)) +
      x / (x + y) * Real.log x +
      (1 - x / (x + y)) * Real.log y = Real.log (x + y) := by
  have hxy : 0 < x + y := add_pos hx hy
  have hcomp : 1 - x / (x + y) = y / (x + y) := by field_simp; ring
  rw [Real.binEntropy, hcomp]
  simp only [Real.log_inv]
  rw [Real.log_div hx.ne' hxy.ne', Real.log_div hy.ne' hxy.ne']
  field_simp
  <;> ring

theorem phi233_optimized_log_rate
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    Real.binEntropy sigma + 2 * Real.binEntropy mu +
        (sigma + 2) * Real.log 2 + 2 * mu * Real.log E +
        sigma * Real.log H + (2 - sigma - 2 * mu) * Real.log L =
      Real.log (4 * (E + L) ^ 2 * (2 * H + L) / L) := by
  dsimp only
  have h2H : 0 < 2 * H := by positivity
  have hEL : 0 < E + L := add_pos hE hL
  have hHL : 0 < 2 * H + L := add_pos h2H hL
  have hs := phi233_binary_optimizer_log (2 * H) L h2H hL
  have hm := phi233_binary_optimizer_log E L hE hL
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hH.ne'] at hs
  rw [Real.log_div (by positivity) hL.ne',
    Real.log_mul (by positivity) hHL.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
    Real.log_pow]
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hfour]
  nlinarith

theorem phi233_multinomial_entropy_lower
    {R : Type*} [Fintype R] (w : R → ℕ) (n : ℕ)
    (hn : 0 < n) (hsum : ∑ i, w i = n) :
    Real.exp ((n : ℝ) * ∑ i, Real.negMulLog ((w i : ℝ) / n)) ≤
      (6 * ((n + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        ((n.factorial / ∏ i, (w i).factorial : ℕ) : ℝ) := by
  have hw : 0 < ∑ i, w i := by omega
  have h := mme_dwz_multinomial_entropy_polynomial_lower w 1 (by omega) hw
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [hsum, Nat.mul_one, mul_one, one_mul, mme_modern_entropyBits] at h
  have hcancel (x : ℝ) : (n : ℝ) * Real.log 2 * (x / Real.log 2) = n * x := by
    field_simp
  rw [hcancel] at h
  simpa only [Nat.multinomial, hsum, Nat.cast_one, one_mul] using h

theorem phi233_marginal_totals
    (alpha beta gamma delta : ℕ) (i : Fin 3) :
    ∑ s : Fin 5, marginalMultiplicity alpha beta gamma delta i s =
      2 * (2 * alpha + beta + gamma + delta) := by
  fin_cases i <;> norm_num [marginalMultiplicity, Fin.sum_univ_succ] <;> omega

theorem phi233_marginal_entropy_formula
    (a b c d : ℝ) (htotal : 2 * a + b + c + d = 1) :
    (2 * Real.negMulLog ((2 * a + b) / 2) + Real.negMulLog (c + d)) +
        2 * (2 * Real.negMulLog ((a + c) / 2) +
          2 * Real.negMulLog ((a + b + d) / 2)) =
      Real.binEntropy (2 * a + b) + 2 * Real.binEntropy (a + c) +
        (2 * a + b + 2) * Real.log 2 := by
  have hn (x : ℝ) : 2 * Real.negMulLog (x / 2) =
      Real.negMulLog x + x * Real.log 2 := by
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    norm_num [Real.negMulLog, Real.log_div, Real.log_inv]
    ring
  rw [hn, hn, hn]
  have hc : c + d = 1 - (2 * a + b) := by linarith
  have hd : a + b + d = 1 - (a + c) := by linarith
  rw [hc, hd, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

noncomputable def phi233_component_rates (E H L : ℝ) : Fin 10 → ℝ :=
  ![E * H, H * L, E * H, E ^ 2, L ^ 2, L ^ 2, E ^ 2, E * H, H * L, E * H]

noncomputable def phi233_log_rate (E H L a b c d : ℝ) : ℝ :=
  (2 * Real.negMulLog ((2 * a + b) / 2) + Real.negMulLog (c + d)) +
    2 * (2 * Real.negMulLog ((a + c) / 2) +
      2 * Real.negMulLog ((a + b + d) / 2)) +
    (2 * a + 2 * c) * Real.log E + (2 * a + b) * Real.log H +
    (b + 2 * d) * Real.log L

theorem phi233_finite_entropy_bound
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L)
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    Real.exp ((2 * N : ℝ) *
      phi233_log_rate E H L (alpha / N) (beta / N) (gamma / N) (delta / N)) ≤
      (6 * ((2 * N + 1 : ℕ) : ℝ)) ^ 15 *
        (∏ i : Fin 3,
          (((2 * N).factorial / ∏ s : Fin 5,
            (marginalMultiplicity alpha beta gamma delta i s).factorial : ℕ) : ℝ)) *
        (∏ r : Fin 10, phi233_component_rates E H L r ^
          profileMultiplicity alpha beta gamma delta r) := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  let ent (i : Fin 3) := ∑ s : Fin 5,
    Real.negMulLog ((marginalMultiplicity alpha beta gamma delta i s : ℝ) / (2 * N))
  let mm (i : Fin 3) : ℝ :=
    ((2 * N).factorial / ∏ s : Fin 5,
      (marginalMultiplicity alpha beta gamma delta i s).factorial : ℕ)
  have hbound (i : Fin 3) :
      Real.exp ((2 * N : ℝ) * ent i) ≤
        (6 * ((2 * N + 1 : ℕ) : ℝ)) ^ 5 * mm i := by
    have hi := phi233_multinomial_entropy_lower
      (marginalMultiplicity alpha beta gamma delta i) (2 * N) (by omega)
      (by rw [phi233_marginal_totals, hsum])
    simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, ent, mm] using hi
  have hp := Finset.prod_le_prod
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ (Real.exp_pos _).le)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ hbound i)
  rw [← Real.exp_sum] at hp
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul] at hp
  norm_num only [Nat.reduceMul] at hp
  let B := ∏ r : Fin 10, phi233_component_rates E H L r ^
    profileMultiplicity alpha beta gamma delta r
  have hr (r : Fin 10) : 0 < phi233_component_rates E H L r := by
    fin_cases r <;> simp [phi233_component_rates] <;> positivity
  have hB : 0 < B := Finset.prod_pos (fun r _ ↦ pow_pos (hr r) _)
  have hlogB : Real.log B =
      (4 * alpha + 4 * gamma : ℝ) * Real.log E +
      (4 * alpha + 2 * beta : ℝ) * Real.log H +
      (2 * beta + 4 * delta : ℝ) * Real.log L := by
    dsimp only [B]
    rw [Real.log_prod (fun r _ ↦ (pow_pos (hr r) _).ne')]
    simp only [Real.log_pow]
    norm_num [Fin.sum_univ_succ, phi233_component_rates, profileMultiplicity,
      Real.log_mul hE.ne' hH.ne', Real.log_mul hH.ne' hL.ne', Real.log_pow]
    ring
  have hent : (∑ i : Fin 3, (2 * N : ℝ) * ent i) + Real.log B =
      (2 * N : ℝ) *
        phi233_log_rate E H L (alpha / N) (beta / N) (gamma / N) (delta / N) := by
    rw [hlogB]
    simp only [ent, phi233_log_rate]
    norm_num [Fin.sum_univ_succ, marginalMultiplicity, Nat.cast_add, Nat.cast_mul]
    have h1 : ((2 * gamma + 2 * delta : ℝ) / (2 * N)) = gamma / N + delta / N := by ring
    have h2 : ((2 * alpha + beta : ℝ) / (2 * N)) = (2 * (alpha / N) + beta / N) / 2 := by ring
    have h3 : ((alpha + gamma : ℝ) / (2 * N)) = (alpha / N + gamma / N) / 2 := by ring
    have h4 : ((alpha + beta + delta : ℝ) / (2 * N)) =
        (alpha / N + beta / N + delta / N) / 2 := by ring
    rw [h1, h2, h3, h4]
    field_simp
    <;> ring
  have h := mul_le_mul_of_nonneg_right hp hB.le
  rw [← Real.exp_log hB, ← Real.exp_add, hent] at h
  simpa only [Real.exp_log hB, mm, B] using h

open MME BigOperators Filter
open MME.StothersFourth.Phi233
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem phi233_stationary_profile (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∃ a b c d : ℝ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      2 * a + b + c + d = 1 ∧
      (2 * (-Real.log (a / 2) - 1) - 2 * (-Real.log (b / 2) - 1) -
        (-Real.log (c / 2) - 1) + (-Real.log (d / 2) - 1) = 0) ∧
      2 * a + b < 2 / 3 ∧ a + c < 1 / 2 ∧
      phi233_log_rate (MME.StothersFourth.E 6 tau)
        (MME.StothersFourth.H 6 tau) (MME.StothersFourth.L 6 tau) a b c d =
        Real.log (MME.StothersFourth.classValue 6 tau 9) := by
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let L := MME.StothersFourth.L 6 tau
  obtain ⟨hE16, hEH, hHL, hLH, _, _⟩ :=
    mme_stothers_q6_EHL_optimizer_regime tau htauLower htauUpper
  have hE : 0 < E := by dsimp [E]; linarith
  have hH : 0 < H := by dsimp [H, E] at *; linarith
  have hL : 0 < L := by dsimp [L, H] at *; linarith
  let sigma := 2 * H / (2 * H + L)
  let mu := E / (E + L)
  have hs0 : 0 < sigma := by dsimp [sigma]; positivity
  have hm0 : 0 < mu := by dsimp [mu]; positivity
  have hs23 : sigma < 2 / 3 := by
    dsimp [sigma]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * H + L)).2
    dsimp [H, L] at *
    linarith
  have hm12 : mu < 1 / 2 := by
    dsimp [mu]
    apply (div_lt_iff₀ (by positivity : 0 < E + L)).2
    dsimp [E, H, L] at *
    linarith
  obtain ⟨a, b, c, d, ha, hb, hc, hd, htotal, hs, hm, hcritical⟩ :=
    mme_stothers_phi233_positive_critical_profile_exists sigma mu hs0 hm0
      (by linarith) (by linarith)
  refine ⟨a, b, c, d, ha, hb, hc, hd, htotal,
    mme_stothers_phi233_log_stationarity_of_critical_product a b c d ha hb hc hd hcritical,
    by linarith, by linarith, ?_⟩
  change phi233_log_rate E H L a b c d = _
  unfold phi233_log_rate
  rw [phi233_marginal_entropy_formula a b c d htotal]
  have hcoeff : b + 2 * d = 2 - (2 * a + b) - 2 * (a + c) := by linarith
  rw [show 2 * a + 2 * c = 2 * (a + c) by ring, hcoeff, hs, hm]
  convert phi233_optimized_log_rate E H L hE hH hL using 1
  rfl

private theorem phi233_log_rate_tendsto
    (E H L a b c d : ℝ) (A B C D : ℕ → ℝ)
    (ha : Tendsto A atTop (nhds a)) (hb : Tendsto B atTop (nhds b))
    (hc : Tendsto C atTop (nhds c)) (hd : Tendsto D atTop (nhds d)) :
    Tendsto (fun n ↦ phi233_log_rate E H L (A n) (B n) (C n) (D n))
      atTop (nhds (phi233_log_rate E H L a b c d)) := by
  unfold phi233_log_rate
  have hneg {f : ℕ → ℝ} {x : ℝ} (h : Tendsto f atTop (nhds x)) :
      Tendsto (fun n ↦ Real.negMulLog (f n)) atTop (nhds (Real.negMulLog x)) :=
    Real.continuous_negMulLog.continuousAt.tendsto.comp h
  have hfirst := ((hneg (((ha.const_mul 2).add hb).div_const 2)).const_mul 2).add
    (hneg (hc.add hd))
  have hsecond := (((hneg ((ha.add hc).div_const 2)).const_mul 2).add
    ((hneg (((ha.add hb).add hd).div_const 2)).const_mul 2)).const_mul 2
  exact ((((hfirst.add hsecond).add
    (((ha.const_mul 2).add (hc.const_mul 2)).mul_const (Real.log E))).add
    (((ha.const_mul 2).add hb).mul_const (Real.log H))).add
    ((hb.add (hd.const_mul 2)).mul_const (Real.log L)))

private theorem phi233_scaled_log_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.log (s * n + 1) / (2 * n)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n)) atTop (nhds (s / 2)) := by
    have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hi).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hl.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    field_simp

private theorem phi233_scaled_sqrt_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.sqrt (s * n + 1) / (2 * n)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ht)
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n)) atTop (nhds (s / 2)) := by
    have hin : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hin).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hi.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    have hsqrt : Real.sqrt (s * n + 1) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    simp only [Function.comp_apply]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le]

private theorem phi233_scalar_from_profile
    (E H L V eps : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L) (hV : 0 < V)
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : ExactProfileAddress N alpha beta gamma delta)
    (hratio :
      (Nat.card (MarginalAddress N alpha beta gamma delta) : ℝ) ≤
        ((2 * N + 1 : ℕ) : ℝ)^10 * Real.exp ((2 * N : ℝ) * eps) *
          (6 * ((2 * N + 1 : ℕ) : ℝ))^10 *
            (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ))
    (hgap :
      (2 * N : ℝ) * Real.log V + 3 * (2 * N : ℝ) * eps +
        (30 * Real.log ((2 * N + 1 : ℕ) : ℝ) +
          45 * Real.log (6 * ((2 * N + 1 : ℕ) : ℝ)) +
          4000 * Real.sqrt ((18 * N + 1 : ℕ) : ℝ)) <
      (2 * N : ℝ) * phi233_log_rate E H L (alpha / N) (beta / N) (gamma / N) (delta / N)) :
    V ^ (2 * N) *
      (∏ l : Fin 3, (Nat.card {b : MarginalAddress N alpha beta gamma delta // b.1 l = a.1.1 l} : ℝ)) *
      Real.exp (4000 * Real.sqrt ((18 * N + 1 : ℕ) : ℝ)) <
      ((targetFinset N alpha beta gamma delta).card : ℝ) *
        (∏ r : Fin 10, phi233_component_rates E H L r ^ profileMultiplicity alpha beta gamma delta r) := by
  let P : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let Q : ℝ := ((18 * N + 1 : ℕ) : ℝ)
  let R : ℝ := P^10 * Real.exp ((2 * N : ℝ) * eps) * (6 * P)^10
  let B := ∏ r : Fin 10, phi233_component_rates E H L r ^ profileMultiplicity alpha beta gamma delta r
  let M := ∏ i : Fin 3, (((2 * N).factorial /
    ∏ s : Fin 5, (marginalMultiplicity alpha beta gamma delta i s).factorial : ℕ) : ℝ)
  let D0 := ∏ l : Fin 3,
    (Nat.card {b : ExactProfileAddress N alpha beta gamma delta // b.1.1 l = a.1.1 l} : ℝ)
  let D1 := ∏ l : Fin 3,
    (Nat.card {b : MarginalAddress N alpha beta gamma delta // b.1 l = a.1.1 l} : ℝ)
  let T : ℝ := ((targetFinset N alpha beta gamma delta).card : ℝ)
  have hP : 0 < P := by dsimp [P]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hM : 0 ≤ M := Finset.prod_nonneg (fun i _ ↦ Nat.cast_nonneg _)
  haveI : Finite (ProfileAddress N) := by unfold ProfileAddress; infer_instance
  haveI : Finite (ExactProfileAddress N alpha beta gamma delta) := by
    unfold ExactProfileAddress MarginalAddress
    infer_instance
  have hD0 : 0 < D0 := by
    apply Finset.prod_pos
    intro l _
    haveI : Nonempty {b : ExactProfileAddress N alpha beta gamma delta // b.1.1 l = a.1.1 l} := ⟨⟨a, rfl⟩⟩
    exact_mod_cast Nat.card_pos
  have hfactor : M * D0 = T := by
    rw [← Finset.prod_mul_distrib]
    have hh (i : Fin 3) := congrArg (fun n : ℕ ↦ (n : ℝ))
      (mme_stothers_phi233_exact_star_factorization N alpha beta gamma delta hsum a i)
    simp only [Nat.cast_mul] at hh
    simp_rw [← hh]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    dsimp [T]
    rw [(mme_stothers_phi233_cyclic_finset_cardinalities N alpha beta gamma delta).2.1,
      Nat.cast_pow]
  have hdegree : D1 ≤ R^3 * D0 := by
    have hh := mme_stothers_phi233_cyclic_star_ratio N alpha beta gamma delta hsum a R hR.le hratio
    simpa only [Nat.cast_prod, D1, D0] using hh
  have hf := phi233_finite_entropy_bound E H L hE hH hL N alpha beta gamma delta hN hsum
  have hexp := Real.exp_lt_exp.mpr hgap
  have hRlog : Real.log R = 10 * Real.log P + (2 * N : ℝ) * eps + 10 * Real.log (6 * P) := by
    dsimp [R]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_pow, Real.log_pow, Real.log_exp]
    norm_num
  have hexponent :
      (2 * N : ℝ) * Real.log V + 3 * (2 * N : ℝ) * eps +
        (30 * Real.log P + 45 * Real.log (6 * P) + 4000 * Real.sqrt Q) =
      Real.log (V^(2 * N) * R^3 * Real.exp (4000 * Real.sqrt Q) * (6 * P)^15) := by
    conv_rhs =>
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_exp, hRlog]
    push_cast
    ring
  change Real.exp ((2 * N : ℝ) * Real.log V + 3 * (2 * N : ℝ) * eps +
    (30 * Real.log P + 45 * Real.log (6 * P) + 4000 * Real.sqrt Q)) < _ at hexp
  rw [hexponent, Real.exp_log (by positivity)] at hexp
  have hc : V^(2*N) * R^3 * Real.exp (4000 * Real.sqrt Q) < M * B := by
    have hh := lt_of_lt_of_le hexp hf
    change _ < (6 * P)^15 * M * B at hh
    have hp15 : 0 < (6 * P)^15 := by positivity
    nlinarith
  have hc' := mul_lt_mul_of_pos_right hc hD0
  change V^(2*N) * D1 * Real.exp (4000 * Real.sqrt Q) < T * B
  calc
    V^(2*N) * D1 * Real.exp (4000 * Real.sqrt Q) ≤
        V^(2*N) * (R^3 * D0) * Real.exp (4000 * Real.sqrt Q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdegree (pow_pos hV _).le)
        (Real.exp_pos _).le
    _ < M * B * D0 := by nlinarith [hc']
    _ = T * B := by rw [mul_assoc, mul_comm B D0, ← mul_assoc, hfactor]

private theorem phi233_penalty_limit :
    Tendsto (fun n : ℕ ↦
      (30 * Real.log ((2 * n + 1 : ℕ) : ℝ) +
        45 * Real.log (6 * ((2 * n + 1 : ℕ) : ℝ)) +
        4000 * Real.sqrt ((18 * n + 1 : ℕ) : ℝ)) / (2 * n))
      atTop (nhds 0) := by
  have hl := phi233_scaled_log_limit 2 (by norm_num)
  have hs := phi233_scaled_sqrt_limit 18 (by norm_num)
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := ((hl.const_mul 30).add
    (((hi.const_mul (Real.log 6)).div_const 2).add hl |>.const_mul 45)).add
    (hs.const_mul 4000)
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hp]
    ring

private theorem phi233_surplus_positive (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 < V) (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ 2 * alpha + beta + gamma + delta = N ∧
      ∃ a : ExactProfileAddress N alpha beta gamma delta,
        V ^ (2 * N) *
          (∏ l : Fin 3, (Nat.card {b : MarginalAddress N alpha beta gamma delta // b.1 l = a.1.1 l} : ℝ)) *
          Real.exp (4000 * Real.sqrt ((18 * N + 1 : ℕ) : ℝ)) <
          ((targetFinset N alpha beta gamma delta).card : ℝ) *
            (∏ r : Fin 10, phi233_component_rates
              (MME.StothersFourth.E 6 tau) (MME.StothersFourth.H 6 tau) (MME.StothersFourth.L 6 tau) r ^
                profileMultiplicity alpha beta gamma delta r) := by
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let L := MME.StothersFourth.L 6 tau
  let Z := MME.StothersFourth.classValue 6 tau 9
  obtain ⟨hE16, hEH, hHL, _, _, _⟩ := mme_stothers_q6_EHL_optimizer_regime tau htauLower htauUpper
  have hE : 0 < E := by dsimp [E]; linarith
  have hH : 0 < H := by dsimp [H, E] at *; linarith
  have hL : 0 < L := by dsimp [L, H] at *; linarith
  have hlog : Real.log V < Real.log Z := Real.log_lt_log hV hVlt
  let eps := (Real.log Z - Real.log V) / 6
  have heps : 0 < eps := by dsimp [eps]; linarith
  obtain ⟨a, b, c, d, ha, hb, hc, hd, htotal, hstation, hs, hm, hrate⟩ :=
    phi233_stationary_profile tau htauLower htauUpper
  obtain ⟨A, B, C, D, k, hsum, hA, hB, hC, hD, hk, hratio⟩ :=
    mme_stothers_phi233_asymptotic_completion_bridge a b c d ha hb hc hd htotal hstation hs hm
  have ht := phi233_log_rate_tendsto E H L a b c d
    (fun n ↦ A n / (n : ℝ)) (fun n ↦ B n / (n : ℝ))
    (fun n ↦ C n / (n : ℝ)) (fun n ↦ D n / (n : ℝ)) hA hB hC hD
  change Tendsto _ atTop (nhds (phi233_log_rate
    (MME.StothersFourth.E 6 tau) (MME.StothersFourth.H 6 tau) (MME.StothersFourth.L 6 tau) a b c d)) at ht
  rw [hrate] at ht
  have hlim := (ht.sub_const (3 * eps)).sub phi233_penalty_limit
  have hg : Real.log V < Real.log Z - 3 * eps - 0 := by dsimp [eps]; linarith
  have hevent := hlim.eventually (eventually_gt_nhds hg)
  have hshift := (tendsto_add_atTop_nat k).eventually hevent
  obtain ⟨n, hnratio, hngap⟩ := ((hratio eps heps).and hshift).exists
  let N := n + k
  have hN : 0 < N := by dsimp [N]; omega
  have hnreal : 0 < (2 * N : ℝ) := by positivity
  have hgap :
      (2 * N : ℝ) * Real.log V + 3 * (2 * N : ℝ) * eps +
        (30 * Real.log ((2 * N + 1 : ℕ) : ℝ) +
          45 * Real.log (6 * ((2 * N + 1 : ℕ) : ℝ)) +
          4000 * Real.sqrt ((18 * N + 1 : ℕ) : ℝ)) <
        (2 * N : ℝ) * phi233_log_rate E H L (A N / N) (B N / N) (C N / N) (D N / N) := by
    have hh := mul_lt_mul_of_pos_left hngap hnreal
    change (2 * N : ℝ) * Real.log V < (2 * N : ℝ) *
      (phi233_log_rate E H L (A N / N) (B N / N) (C N / N) (D N / N) - 3 * eps -
        (30 * Real.log ((2 * N + 1 : ℕ) : ℝ) +
          45 * Real.log (6 * ((2 * N + 1 : ℕ) : ℝ)) +
          4000 * Real.sqrt ((18 * N + 1 : ℕ) : ℝ)) / (2 * N)) at hh
    field_simp at hh
    nlinarith
  obtain ⟨addr⟩ := mme_stothers_phi233_exact_profile_nonempty N (A N) (B N) (C N) (D N) (hsum N)
  refine ⟨N, A N, B N, C N, D N, hN, hsum N, addr, ?_⟩
  apply phi233_scalar_from_profile E H L V eps hE hH hL hV N (A N) (B N) (C N) (D N)
    hN (hsum N) addr
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnratio
  · exact hgap

theorem solution
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ 2 * alpha + beta + gamma + delta = N ∧
      ∃ a : ExactProfileAddress N alpha beta gamma delta,
        V ^ (2 * N) *
            (∏ l : Fin 3,
              (Nat.card {b : MarginalAddress N alpha beta gamma delta //
                b.1 l = a.1.1 l} : ℝ)) *
            Real.exp (4000 * Real.sqrt (((18 * N + 1 : ℕ) : ℝ))) <
          ((targetFinset N alpha beta gamma delta).card : ℝ) *
            (∏ r : Fin 10,
          (![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau] :
                Fin 10 → ℝ) r ^
            MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r) := by
  let Z := MME.StothersFourth.classValue 6 tau 9
  let W := (V + Z) / 2
  have hVW : V < W := by dsimp [W, Z]; linarith
  have hW : 0 < W := lt_of_le_of_lt hV hVW
  have hWZ : W < MME.StothersFourth.classValue 6 tau 9 := by dsimp [W, Z]; linarith
  obtain ⟨N, alpha, beta, gamma, delta, hN, hsum, a, hstrict⟩ :=
    phi233_surplus_positive tau htauLower htauUpper W hW hWZ
  refine ⟨N, alpha, beta, gamma, delta, hN, hsum, a, lt_of_le_of_lt ?_ hstrict⟩
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_left₀ hV hVW.le _
    · exact Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  · exact (Real.exp_pos _).le
