-- Prove2me | solution 1 for prime_number_theorem_gap
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:33:02.094899+00:00
-- url     : https://prove2.me/submissions/3e1e0a3d-cc3c-426c-a4a6-3a62777075d6

import Mathlib
import Theorems.Thm_MediumPNT

open Filter Asymptotics Topology
open scoped Chebyshev Nat.Prime

/-- `x * exp(-c (log x)^(1/10)) = o(x)` as `x → ∞`. -/
lemma pntgap_isLittleO_mul_exp (c : ℝ) (hc : 0 < c) :
    (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) =o[atTop]
      (fun x : ℝ => x) := by
  have h1 : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Tendsto.const_mul_atTop_of_neg (by linarith)
    exact (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have h2 := (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO ((isLittleO_one_iff ℝ).mpr h1)
  simpa using h2

/-- `ψ(x) ~ x`, from the medium-strength prime number theorem. -/
lemma pntgap_psi_equiv : Chebyshev.psi ~[atTop] id := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  exact hO.trans_isLittleO (pntgap_isLittleO_mul_exp c hc)

lemma pntgap_sqrt_isLittleO : (fun x : ℝ => Real.sqrt x) =o[atTop] (fun x : ℝ => x) := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx h
    exact absurd h hx.ne'
  · have : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    refine this.congr' ?_
    filter_upwards with x
    rw [Real.sqrt_div_self', one_div]

/-- `θ(x) ~ x`. -/
lemma pntgap_theta_equiv : Chebyshev.theta ~[atTop] id := by
  have h : (Chebyshev.theta - Chebyshev.psi) =o[atTop] id := by
    have := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO pntgap_sqrt_isLittleO).neg_left
    exact this.congr_left fun x => by simp [Pi.sub_apply]
  have := pntgap_psi_equiv.add_isLittleO h
  rw [add_sub_cancel] at this
  exact this

lemma pntgap_tendsto_div_log : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have := h1.inv_tendsto_nhdsGT_zero
  refine this.congr' ?_
  filter_upwards with x
  simp [inv_div]

lemma pntgap_div_log_sq_isLittleO :
    (fun x : ℝ => x / Real.log x ^ 2) =o[atTop] (fun x : ℝ => x / Real.log x) := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards with x h
    rcases div_eq_zero_iff.mp h with h | h
    · simp [h]
    · simp [h]
  · refine Tendsto.congr' (f₁ := fun x ↦ (Real.log x)⁻¹) ?_ Real.tendsto_log_atTop.inv_tendsto_atTop
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hx0 : x ≠ 0 := by positivity
    field_simp

/-- `π(⌊x⌋) ~ x / log x`. -/
lemma pntgap_primeCounting_equiv :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x : ℝ => x / Real.log x) := by
  have h1 : (fun x : ℝ => Chebyshev.theta x / Real.log x) ~[atTop]
      (fun x : ℝ => x / Real.log x) :=
    pntgap_theta_equiv.div (IsEquivalent.refl (u := Real.log))
  have h2 := Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO pntgap_div_log_sq_isLittleO
  have := h1.add_isLittleO h2
  refine this.congr_left ?_
  filter_upwards with x
  simp

lemma pntgap_primeCounting'_bounds (n : ℕ) :
    n.primeCounting' ≤ n.primeCounting ∧ n.primeCounting ≤ n.primeCounting' + 1 := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  split_ifs <;> omega

/-- `π'(⌊x⌋) = #{p < ⌊x⌋ prime} ~ x / log x`. -/
lemma pntgap_primeCounting'_equiv :
    (fun x : ℝ => (Nat.primeCounting' ⌊x⌋₊ : ℝ)) ~[atTop] (fun x : ℝ => x / Real.log x) := by
  have h1 : (fun x : ℝ => (Nat.primeCounting' ⌊x⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    obtain ⟨ha, hb⟩ := pntgap_primeCounting'_bounds ⌊x⌋₊
    rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
    constructor
    · have : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Nat.primeCounting' ⌊x⌋₊ + 1 := by exact_mod_cast hb
      linarith
    · have : (Nat.primeCounting' ⌊x⌋₊ : ℝ) ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast ha
      linarith
  have h2 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] (fun x : ℝ => x / Real.log x) :=
    isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp pntgap_tendsto_div_log))
  have := pntgap_primeCounting_equiv.add_isLittleO (h1.trans_isLittleO h2)
  refine this.congr_left ?_
  filter_upwards with x
  simp

lemma pntgap_tendsto_primeCounting'_div :
    Tendsto (fun x : ℝ => (Nat.primeCounting' ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  have hz : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (div_pos (by linarith) (Real.log_pos hx)).ne'
  exact (isEquivalent_iff_tendsto_one hz).mp pntgap_primeCounting'_equiv

theorem solution :
    Filter.Tendsto (fun x : ℝ =>
      (∑ p ∈ (Finset.range (Nat.floor x)).filter Nat.Prime, (1 : ℝ)) /
      (x / Real.log x))
    Filter.atTop (nhds 1) := by
  refine pntgap_tendsto_primeCounting'_div.congr' ?_
  filter_upwards with x
  simp [Nat.primeCounting', Nat.count_eq_card_filter_range]
