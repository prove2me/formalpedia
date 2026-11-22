-- Prove2me | solution 1 for dirichlet_boundary_convergence_and_error_of_log_squared_saving
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T13:02:36.718247+00:00
-- url     : https://prove2.me/submissions/2c12a863-3ea1-4153-94ba-44f03cfd44fe

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

set_option autoImplicit false

open Finset Filter Complex MeasureTheory Asymptotics
open scoped Topology

namespace BoundaryDirichletD26.Mertens

noncomputable def summatoryReal (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

noncomputable def mellinExtension (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * mellin (summatoryReal f) (-s)

lemma summatoryReal_eq_zero {f : ℕ → ℂ} {t : ℝ} (ht : t < 1) :
    summatoryReal f t = 0 := by
  simp [summatoryReal, Nat.floor_eq_zero.mpr ht]

theorem mellin_summatoryReal_neg_eq_integral (f : ℕ → ℂ) (s : ℂ) :
    mellin (summatoryReal f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), summatoryReal f t * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  have hcut :
      (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • summatoryReal f t) =
      ∫ t in Set.Ici (1 : ℝ), (t : ℂ) ^ (-s - 1) • summatoryReal f t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    · intro t ht
      exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) ht
    · intro t ht
      have ht1 : t < 1 := lt_of_not_ge ht.2
      rw [summatoryReal_eq_zero ht1, smul_zero]
  rw [hcut, integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [smul_eq_mul, show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma sum_Icc_zero_eq_sum_Icc_one {f : ℕ → ℂ} (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := by
  rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp), hf, zero_add,
    zero_add]

theorem dirichlet_partialSum_eq (f : ℕ → ℂ) (hf : f 0 = 0)
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ∑ k ∈ Icc 1 N, f k / (k : ℂ) ^ s =
      (N : ℂ) ^ (-s) * (∑ k ∈ Icc 1 N, f k) +
      s * ∫ t in Set.Ioc (1 : ℝ) N, summatoryReal f t * (t : ℂ) ^ (-(s + 1)) := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) N) :
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne'
      (neg_ne_zero.mpr hs0)
  have hint : LocallyIntegrableOn (deriv (fun x : ℝ => (x : ℂ) ^ (-s))) (Set.Ici 1) :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by simpa using hs))).locallyIntegrableOn
  have hid := sum_mul_eq_sub_integral_mul₀' f hf N hdiff
    (hint.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)
  have hsum (n : ℕ) :
      ∑ k ∈ Icc 0 n, (k : ℂ) ^ (-s) * f k = ∑ k ∈ Icc 1 n, f k / (k : ℂ) ^ s := by
    rw [sum_Icc_zero_eq_sum_Icc_one (by simp [hf])]
    apply sum_congr rfl
    intro k hk
    rw [cpow_neg, div_eq_mul_inv, mul_comm]
  have hderiv :
      (∫ t in Set.Ioc (1 : ℝ) N,
        deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      -s * ∫ t in Set.Ioc (1 : ℝ) N,
        summatoryReal f t * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht.1).ne',
      sum_Icc_zero_eq_sum_Icc_one hf]
    · dsimp only [summatoryReal]
      ring_nf
    · exact neg_ne_zero.mpr hs0
  rw [hderiv] at hid
  simpa only [Complex.ofReal_natCast, hsum, sum_Icc_zero_eq_sum_Icc_one hf,
    neg_mul, sub_neg_eq_add] using hid

end BoundaryDirichletD26.Mertens

open Complex Filter MeasureTheory Asymptotics
open scoped Topology

namespace BoundaryDirichletD26.Boundary

lemma kernel_norm_le_log (f : ℕ → ℂ) {r C : ℝ} {s : ℂ} (hs : s.re = r)
    (hM : ∀ t : ℝ, 2 ≤ t →
      ‖BoundaryDirichletD26.Mertens.summatoryReal f t‖ ≤ C * t ^ r / (Real.log t) ^ 2)
    {t : ℝ} (ht : 2 ≤ t) :
    ‖BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1))‖ ≤
      C * (t⁻¹ / (Real.log t) ^ 2) := by
  have ht0 : 0 < t := by linarith
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, neg_re, add_re, one_re, hs]
  calc
    ‖BoundaryDirichletD26.Mertens.summatoryReal f t‖ * t ^ (-(r + 1)) ≤
        (C * t ^ r / (Real.log t) ^ 2) * t ^ (-(r + 1)) :=
      mul_le_mul_of_nonneg_right (hM t ht) (Real.rpow_nonneg ht0.le _)
    _ = C * (t⁻¹ / (Real.log t) ^ 2) := by
      rw [div_mul_eq_mul_div, mul_assoc, ← Real.rpow_add ht0]
      rw [show r + -(r + 1) = -1 by ring, Real.rpow_neg_one]
      ring

theorem integrable_kernel_of_log_bound (f : ℕ → ℂ) {r C : ℝ} {s : ℂ}
    (hs : s.re = r)
    (hM : ∀ t : ℝ, 2 ≤ t →
      ‖BoundaryDirichletD26.Mertens.summatoryReal f t‖ ≤ C * t ^ r / (Real.log t) ^ 2) :
    IntegrableOn (fun t : ℝ =>
      BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := by
    intro t ht
    exact (continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (by have : 0 < t := zero_lt_one.trans_le ht; exact this.ne'))).continuousWithinAt
  have hlocal := locallyIntegrableOn_mul_sum_Icc f (m := 1) (a := 1) zero_le_one
    (hcont.locallyIntegrableOn measurableSet_Ici)
  have hlocal' : LocallyIntegrableOn (fun t : ℝ =>
      BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := by
    simpa only [BoundaryDirichletD26.Mertens.summatoryReal, mul_comm] using hlocal
  have hO : (fun t : ℝ => BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1)))
      =O[atTop] (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop 2] with t ht
    have ht0 : 0 < t := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (inv_nonneg.mpr ht0.le)
      (sq_nonneg (Real.log t)))] using kernel_norm_le_log f hs hM ht
  have hi : IntegrableAtFilter (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) atTop :=
    ⟨Set.Ioi 2, Ioi_mem_atTop 2, integrableOn_inv_div_log_sq_Ioi (by norm_num)⟩
  exact (hlocal'.integrableOn_of_isBigO_atTop hO hi).mono_set Set.Ioi_subset_Ici_self

theorem dirichlet_error_of_integrable (f : ℕ → ℂ) (hf : f 0 = 0)
    {s : ℂ} (hs : 0 < s.re)
    (hi : IntegrableOn (fun t : ℝ =>
      BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    {N : ℕ} (hN : 1 ≤ N) :
    BoundaryDirichletD26.Mertens.mellinExtension f s - (∑ k ∈ Finset.Icc 1 N, f k / (k : ℂ) ^ s) =
      -(N : ℂ) ^ (-s) * (∑ k ∈ Finset.Icc 1 N, f k) +
      s * ∫ t in Set.Ioi (N : ℝ),
        BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1)) := by
  rw [BoundaryDirichletD26.Mertens.mellinExtension, BoundaryDirichletD26.Mertens.mellin_summatoryReal_neg_eq_integral,
    BoundaryDirichletD26.Mertens.dirichlet_partialSum_eq f hf hs]
  have hint := intervalIntegral.integral_Ioi_sub_Ioi (b := (N : ℝ)) hi
    (by exact_mod_cast hN)
  rw [intervalIntegral.integral_of_le (by exact_mod_cast hN)] at hint
  rw [← hint]
  ring

lemma norm_tail_of_log_bound (f : ℕ → ℂ) {r C : ℝ} {s : ℂ} (hs : s.re = r)
    (hM : ∀ t : ℝ, 2 ≤ t →
      ‖BoundaryDirichletD26.Mertens.summatoryReal f t‖ ≤ C * t ^ r / (Real.log t) ^ 2)
    {a : ℝ} (ha : 2 ≤ a) :
    ‖s * ∫ t in Set.Ioi a,
      BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * ‖s‖ / Real.log a := by
  have ha1 : 1 < a := by linarith
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi a),
      ‖BoundaryDirichletD26.Mertens.summatoryReal f t * (t : ℂ) ^ (-(s + 1))‖ ≤
        C * (t⁻¹ / (Real.log t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact kernel_norm_le_log f hs hM (ha.trans ht.le)
  have hnorm := norm_integral_le_of_norm_le
    ((integrableOn_inv_div_log_sq_Ioi ha1).const_mul C) hbound
  rw [integral_const_mul, integral_inv_div_log_sq_Ioi ha1] at hnorm
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg s)).trans_eq (by ring)

theorem dirichlet_boundary_error_of_log_bound (f : ℕ → ℂ) (hf : f 0 = 0)
    {r C : ℝ} (hr : 0 < r) {s : ℂ} (hs : s.re = r)
    (hM : ∀ t : ℝ, 2 ≤ t →
      ‖BoundaryDirichletD26.Mertens.summatoryReal f t‖ ≤ C * t ^ r / (Real.log t) ^ 2)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖BoundaryDirichletD26.Mertens.mellinExtension f s - (∑ k ∈ Finset.Icc 1 N, f k / (k : ℂ) ^ s)‖ ≤
      C / (Real.log (N : ℝ)) ^ 2 + C * ‖s‖ / Real.log (N : ℝ) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hMN : ‖∑ k ∈ Finset.Icc 1 N, f k‖ ≤ C * (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2 := by
    simpa only [BoundaryDirichletD26.Mertens.summatoryReal, Nat.floor_natCast] using hM N hNr
  have hpower : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-r) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hN0, neg_re, hs]
  have hend : ‖-(N : ℂ) ^ (-s) * (∑ k ∈ Finset.Icc 1 N, f k)‖ ≤
      C / (Real.log (N : ℝ)) ^ 2 := by
    rw [norm_mul, norm_neg, hpower]
    calc
      (N : ℝ) ^ (-r) * ‖∑ k ∈ Finset.Icc 1 N, f k‖ ≤
          (N : ℝ) ^ (-r) * (C * (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hMN (Real.rpow_nonneg hN0.le _)
      _ = C * ((N : ℝ) ^ (-r) * (N : ℝ) ^ r) / (Real.log (N : ℝ)) ^ 2 := by ring
      _ = C / (Real.log (N : ℝ)) ^ 2 := by
        rw [← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero, mul_one]
  rw [dirichlet_error_of_integrable f hf (by rwa [hs])
    (integrable_kernel_of_log_bound f hs hM) (by omega : 1 ≤ N)]
  exact (norm_add_le _ _).trans (add_le_add hend (norm_tail_of_log_bound f hs hM hNr))

theorem tendsto_dirichlet_boundary_of_log_bound (f : ℕ → ℂ) (hf : f 0 = 0)
    {r C : ℝ} (hr : 0 < r) {s : ℂ} (hs : s.re = r)
    (hM : ∀ t : ℝ, 2 ≤ t →
      ‖BoundaryDirichletD26.Mertens.summatoryReal f t‖ ≤ C * t ^ r / (Real.log t) ^ 2) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, f k / (k : ℂ) ^ s)
      atTop (𝓝 (BoundaryDirichletD26.Mertens.mellinExtension f s)) := by
  have hl : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => C / (Real.log (N : ℝ)) ^ 2 +
      C * ‖s‖ / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, ← inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_add] using ((hl.pow 2).const_mul C).add (hl.const_mul (C * ‖s‖))
  have herr : Tendsto (fun N : ℕ => BoundaryDirichletD26.Mertens.mellinExtension f s -
      (∑ k ∈ Finset.Icc 1 N, f k / (k : ℂ) ^ s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact dirichlet_boundary_error_of_log_bound f hf hr hs hM hN
  have h := (tendsto_const_nhds (x := BoundaryDirichletD26.Mertens.mellinExtension f s)).sub herr
  simpa only [sub_sub_cancel, sub_zero] using h

end BoundaryDirichletD26.Boundary

open Complex Filter Set Asymptotics
open scoped Topology

namespace BoundaryDirichletD26.Mertens

theorem summatoryReal_log_sq_bound_of_discrete
    (f : ℕ → ℂ) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 2 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤
        C * (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2)
    {t : ℝ} (ht : 2 ≤ t) :
    ‖summatoryReal f t‖ ≤ 4 * C * t ^ r / (Real.log t) ^ 2 := by
  have hN : 2 ≤ ⌊t⌋₊ := Nat.le_floor ht
  have hNreal : (2 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by linarith
  have htpos : 0 < t := by linarith
  have hlogN : 0 < Real.log (⌊t⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have htfloor : t ≤ 2 * (⌊t⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one t
    linarith
  have hlog : Real.log t ≤ 2 * Real.log (⌊t⌋₊ : ℝ) := by
    calc
      Real.log t ≤ Real.log (2 * (⌊t⌋₊ : ℝ)) := Real.log_le_log htpos htfloor
      _ = Real.log 2 + Real.log (⌊t⌋₊ : ℝ) :=
        Real.log_mul (by norm_num) hNpos.ne'
      _ ≤ 2 * Real.log (⌊t⌋₊ : ℝ) := by
        have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNreal
        linarith
  have hlogsq : (Real.log t) ^ 2 ≤ 4 * (Real.log (⌊t⌋₊ : ℝ)) ^ 2 := by
    have hsquare := mul_self_le_mul_self hlogt.le hlog
    nlinarith
  have hpow : (⌊t⌋₊ : ℝ) ^ r ≤ t ^ r :=
    Real.rpow_le_rpow hNpos.le (Nat.floor_le htpos.le) hr
  calc
    ‖summatoryReal f t‖ ≤ C * (⌊t⌋₊ : ℝ) ^ r /
        (Real.log (⌊t⌋₊ : ℝ)) ^ 2 := hbound _ hN
    _ ≤ C * t ^ r / (Real.log (⌊t⌋₊ : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (sq_nonneg _)
    _ ≤ 4 * C * t ^ r / (Real.log t) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hlogN) (sq_pos_of_pos hlogt)).mpr
      calc
        C * t ^ r * (Real.log t) ^ 2 ≤
            C * t ^ r * (4 * (Real.log (⌊t⌋₊ : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hlogsq (mul_nonneg hC (Real.rpow_nonneg htpos.le r))
        _ = 4 * C * t ^ r * (Real.log (⌊t⌋₊ : ℝ)) ^ 2 := by ring

end BoundaryDirichletD26.Mertens

open Complex Filter Set Asymptotics
open scoped Topology

namespace BoundaryDirichletD26.Boundary


theorem dirichlet_boundary_of_discrete_log_bound
    (f : ℕ → ℂ) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 2 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤
        C * (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2)
    {s : ℂ} (hs : s.re = r) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)
        atTop (𝓝 (BoundaryDirichletD26.Mertens.mellinExtension f s)) ∧
      ∀ N : ℕ, 2 ≤ N →
        ‖BoundaryDirichletD26.Mertens.mellinExtension f s -
          (∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)‖ ≤
          4 * C / (Real.log (N : ℝ)) ^ 2 +
            4 * C * ‖s‖ / Real.log (N : ℝ) := by
  let f₀ : ℕ → ℂ := fun n => if n = 0 then 0 else f n
  have hf₀ : f₀ 0 = 0 := by simp [f₀]
  have hsum (N : ℕ) :
      ∑ n ∈ Finset.Icc 1 N, f₀ n = ∑ n ∈ Finset.Icc 1 N, f n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact if_neg (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1).ne'
  have hreal : BoundaryDirichletD26.Mertens.summatoryReal f₀ = BoundaryDirichletD26.Mertens.summatoryReal f := by
    funext t
    exact hsum ⌊t⌋₊
  have hF : BoundaryDirichletD26.Mertens.mellinExtension f₀ = BoundaryDirichletD26.Mertens.mellinExtension f := by
    funext z
    simp only [BoundaryDirichletD26.Mertens.mellinExtension, hreal]
  have hpartial (N : ℕ) :
      (∑ n ∈ Finset.Icc 1 N, f₀ n / (n : ℂ) ^ s) =
        ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [show f₀ n = f n from
      if_neg (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1).ne']
  have hbound₀ : ∀ N : ℕ, 2 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f₀ n‖ ≤
        C * (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2 := by
    intro N hN
    simpa only [hsum] using hbound N hN
  have hM : ∀ t : ℝ, 2 ≤ t →
      ‖BoundaryDirichletD26.Mertens.summatoryReal f₀ t‖ ≤
        (4 * C) * t ^ r / (Real.log t) ^ 2 :=
    fun _ ht => BoundaryDirichletD26.Mertens.summatoryReal_log_sq_bound_of_discrete
      f₀ hr.le hC hbound₀ ht
  constructor
  · simpa only [hF, hpartial] using
      tendsto_dirichlet_boundary_of_log_bound f₀ hf₀ hr hs hM
  · intro N hN
    simpa only [hF, hpartial] using
      dirichlet_boundary_error_of_log_bound f₀ hf₀ hr hs hM hN

end BoundaryDirichletD26.Boundary

theorem solution
    (f : ℕ → ℂ) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 2 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤
        C * (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2)
    {s : ℂ} (hs : s.re = r) :
    let F := fun z : ℂ =>
      z * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-z)
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)
      Filter.atTop (nhds (F s)) ∧
    ∀ N : ℕ, 2 ≤ N →
      ‖F s - (∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)‖ ≤
        4 * C / (Real.log (N : ℝ)) ^ 2 + 4 * C * ‖s‖ / Real.log (N : ℝ) := by
  simpa only [BoundaryDirichletD26.Mertens.mellinExtension,
    show BoundaryDirichletD26.Mertens.summatoryReal f = (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) from rfl] using
    BoundaryDirichletD26.Boundary.dirichlet_boundary_of_discrete_log_bound f hr hC hbound hs
