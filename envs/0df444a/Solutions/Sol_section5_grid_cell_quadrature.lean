-- Prove2me | solution 1 for section5_grid_cell_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:08.070482+00:00
-- url     : https://prove2.me/submissions/627db128-8a10-45b8-9f6d-2ca193a5527c

import Mathlib
section
set_option autoImplicit false

open MeasureTheory Set









/-!
The one-dimensional cell estimate used in Appendix D of the LTF paper. This proof
uses the fundamental theorem of calculus and Cauchy--Schwarz, and is valid for
complex-valued functions (indeed, for any complete real normed space).
-/

theorem section5_interval_cauchy_schwarz (g : ℝ → ℝ) (hg : Continuous g)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, g x)^2 ≤ (b-a) * ∫ x in a..b, (g x)^2 := by
  rcases hab.eq_or_lt with h | h
  · subst b
    simp
  · let m := (∫ x in a..b, g x)/(b-a)
    have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable _ _
    have his : IntervalIntegrable (fun x => (g x)^2) volume a b :=
      (hg.pow 2).intervalIntegrable _ _
    have hid : IntervalIntegrable (fun x => (g x-m)^2) volume a b :=
      ((hg.sub continuous_const).pow 2).intervalIntegrable _ _
    have hn : 0 ≤ ∫ x in a..b, (g x-m)^2 :=
      intervalIntegral.integral_nonneg h.le (fun x _ => sq_nonneg _)
    have heq : (∫ x in a..b, (g x-m)^2) =
        (∫ x in a..b, (g x)^2) - 2*m*(∫ x in a..b, g x) + m^2*(b-a) := by
      have hf : (fun x => (g x-m)^2) = fun x => (g x)^2 - (2*m)*g x + m^2 := by
        funext x
        ring
      rw [hf, intervalIntegral.integral_add (his.sub (hi.const_mul _))
        intervalIntegrable_const, intervalIntegral.integral_sub his (hi.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [heq] at hn
    have hlen : 0 < b-a := sub_pos.mpr h
    have hm : m*(b-a) = ∫ x in a..b, g x := by
      dsimp [m]
      exact div_mul_cancel₀ _ hlen.ne'
    have hn' := mul_nonneg hn hlen.le
    nlinarith [sq_nonneg (∫ x in a..b, g x)]

theorem section5_cell_point_error {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f g : ℝ → E)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (a b x : ℝ) (hx : x ∈ Icc a b) :
    ‖f x-f a‖^2 ≤ (b-a) * ∫ y in a..b, ‖g y‖^2 := by
  have hftc : (∫ y in a..x, g y) = f x-f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hf y)
      (hg.intervalIntegrable _ _)
  have hnorm : ‖f x-f a‖ ≤ ∫ y in a..x, ‖g y‖ := by
    rw [← hftc]
    exact intervalIntegral.norm_integral_le_integral_norm hx.1
  have hint : 0 ≤ ∫ y in a..x, ‖g y‖ :=
    intervalIntegral.integral_nonneg hx.1 (fun y _ => norm_nonneg _)
  have hcs := section5_interval_cauchy_schwarz (fun y => ‖g y‖) hg.norm a x hx.1
  have hmono : (∫ y in a..x, ‖g y‖^2) ≤ ∫ y in a..b, ‖g y‖^2 := by
    exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall (fun y => sq_nonneg ‖g y‖))
      ((hg.norm.pow 2).intervalIntegrable _ _)
  have hnonneg : 0 ≤ ∫ y in a..x, ‖g y‖^2 :=
    intervalIntegral.integral_nonneg hx.1 (fun y _ => sq_nonneg _)
  calc
    _ ≤ (∫ y in a..x, ‖g y‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (x-a)*(∫ y in a..x, ‖g y‖^2) := hcs
    _ ≤ (b-a)*(∫ y in a..x, ‖g y‖^2) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 _) hnonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by linarith [hx.1,hx.2])

theorem section5_cell_quadrature {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f g : ℝ → E)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, ‖f x-f a‖^2) ≤ (b-a)^2 * ∫ y in a..b, ‖g y‖^2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have herr : Continuous (fun x => ‖f x-f a‖^2) :=
    ((hfc.sub continuous_const).norm.pow 2)
  calc
    _ ≤ ∫ _x in a..b, (b-a)*(∫ y in a..b, ‖g y‖^2) := by
      apply intervalIntegral.integral_mono_on hab (herr.intervalIntegrable _ _)
        intervalIntegrable_const
      intro x hx
      exact section5_cell_point_error f g hf hg a b x hx
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring





end
set_option autoImplicit false
open MeasureTheory Set
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f g : ℝ → E)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (a δ : ℝ) (hδ : 0 ≤ δ) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      ∫ x in (a+j*δ)..(a+(j+1)*δ), ‖f x-f (a+j*δ)‖^2) ≤
      δ^2 * ∫ y in a..(a+N*δ), ‖g y‖^2 := by
  have hcell (j : ℕ) :
      (∫ x in (a+j*δ)..(a+(j+1)*δ), ‖f x-f (a+j*δ)‖^2) ≤
        δ^2 * ∫ y in (a+j*δ)..(a+(j+1)*δ), ‖g y‖^2 := by
    have hlen : a+((j:ℝ)+1)*δ-(a+j*δ) = δ := by ring
    simpa only [hlen] using section5_cell_quadrature f g hf hg
      (a+j*δ) (a+(j+1)*δ) (by nlinarith)
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        δ^2 * ∫ y in (a+j*δ)..(a+(j+1)*δ), ‖g y‖^2 := by
      exact Finset.sum_le_sum (fun j hj => hcell j)
    _ = δ^2 * ∫ y in a..(a+N*δ), ‖g y‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      have hs := intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j : ℕ => a+j*δ) (n := N)
        (f := fun y => ‖g y‖^2) (μ := volume)
        (fun j _ => (hg.norm.pow 2).intervalIntegrable _ _)
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using hs
