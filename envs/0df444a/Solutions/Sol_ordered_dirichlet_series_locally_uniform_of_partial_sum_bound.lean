-- Prove2me | solution 1 for ordered_dirichlet_series_locally_uniform_of_partial_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:49:41.808077+00:00
-- url     : https://prove2.me/submissions/758c880d-bd39-41de-a646-253490946e2a

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum

section SourceContinuation

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHMertens

noncomputable def summatoryReal (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

noncomputable def mellinExtension (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * mellin (summatoryReal f) (-s)

lemma summatoryReal_eq_zero {f : ℕ → ℂ} {t : ℝ} (ht : t < 1) :
    summatoryReal f t = 0 := by
  simp [summatoryReal, Nat.floor_eq_zero.mpr ht]

lemma locallyIntegrableOn_summatoryReal (f : ℕ → ℂ) :
    LocallyIntegrableOn (summatoryReal f) (Ioi 0) := by
  have hconstant : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ici 0) :=
    continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hstep := locallyIntegrableOn_mul_sum_Icc f (m := 1) (a := 0) le_rfl hconstant
  have hstep' : LocallyIntegrableOn (summatoryReal f) (Ici 0) := by
    change LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) (Ici 0)
    simpa only [one_mul] using hstep
  exact hstep'.mono_set Ioi_subset_Ici_self

lemma summatoryReal_isBigO_atTop {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) :
    summatoryReal f =O[atTop] (fun t : ℝ => t ^ r) := by
  exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans
    (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))

lemma summatoryReal_isBigO_atZero (f : ℕ → ℂ) (b : ℝ) :
    summatoryReal f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] 0] summatoryReal f := by
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with t ht
    exact (summatoryReal_eq_zero ht).symm
  exact (isBigO_zero (fun t : ℝ => t ^ (-b)) (𝓝[>] 0)).congr' heq Filter.EventuallyEq.rfl

theorem differentiableAt_mellinExtension_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r))
    {s : ℂ} (hs : r < s.re) :
    DifferentiableAt ℂ (mellinExtension f) s := by
  have htop : summatoryReal f =O[atTop] (fun t : ℝ => t ^ (-(-r))) := by
    simpa using summatoryReal_isBigO_atTop hr hO
  have hd : DifferentiableAt ℂ (mellin (summatoryReal f)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_summatoryReal f)
      htop (by simp only [neg_re]; linarith)
      (summatoryReal_isBigO_atZero f (-s.re - 1)) (by simp only [neg_re]; linarith)
  exact differentiableAt_id.mul (hd.comp s differentiableAt_id.neg)

theorem differentiableOn_mellinExtension_of_mertens
    {f : ℕ → ℂ}
    (hO : ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 + ε))) :
    DifferentiableOn ℂ (mellinExtension f) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have heps : 0 < (s.re - 1 / 2) / 2 := by
    change 1 / 2 < s.re at hs
    linarith
  exact (differentiableAt_mellinExtension_of_partialSums
    (by linarith : 0 ≤ 1 / 2 + (s.re - 1 / 2) / 2)
    (hO _ heps) (by change 1 / 2 < s.re at hs; linarith)).differentiableWithinAt

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

theorem mellinExtension_eq_LSeries (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    {s : ℂ} (hs : r < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      fun n => (n : ℝ) ^ r) :
    mellinExtension f s = LSeries f s := by
  rw [mellinExtension, mellin_summatoryReal_neg_eq_integral]
  exact (LSeries_eq_mul_integral f hr hs hS hO).symm

theorem mellinExtension_moebius_eq
    (hMertens : ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 / 2 + ε))
    {s : ℂ} (hs : 1 < s.re) :
    mellinExtension (fun n => (ArithmeticFunction.moebius n : ℂ)) s =
      LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  apply mellinExtension_eq_LSeries (r := 1 / 2 + 1 / 4)
  · norm_num
  · linarith
  · exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  · exact hMertens (1 / 4) (by norm_num)

theorem extension_of_mertens
    (hMertens : ∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s := by
  refine ⟨mellinExtension (fun n => (ArithmeticFunction.moebius n : ℂ)),
    differentiableOn_mellinExtension_of_mertens hMertens, ?_⟩
  exact fun _ hs => mellinExtension_moebius_eq hMertens hs

end RHMertens

end SourceContinuation

section SourceOrdered

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

/-!
Ordered Dirichlet-series convergence from cancellation in signed partial sums.
The convergence proof adapts the Abel-summation argument used in Mathlib's
`LSeries_eq_mul_integral`, without requiring `LSeriesSummable`.
The truncation estimate also gives locally uniform convergence on the
half-plane to the right of the partial-sum growth exponent.
-/

namespace RHMertens

private lemma sum_Icc_zero_eq_sum_Icc_one {f : ℕ → ℂ} (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := by
  rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp), hf, zero_add,
    zero_add]

private theorem tendsto_dirichlet_sum_of_partialSums_aux
    {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 1 n, f k / (k : ℂ) ^ s) atTop
      (𝓝 (s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) :
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr h₂)
  have h₄ : ∀ n, ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k :=
    sum_Icc_zero_eq_sum_Icc_one hf
  simp_rw [← h₄] at hO
  have hlim := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := f)
    (f := fun x : ℝ => (x : ℂ) ^ (-s)) (l := 0) hf h₃
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by simpa using hr.trans_lt hs))).locallyIntegrableOn
  have hboundary : Tendsto (fun n : ℕ => (n : ℂ) ^ (-s) * ∑ k ∈ Icc 0 n, f k)
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hpow
    · exact isBigO_norm_left.mp <| (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  have hderiv :
      (fun t : ℝ => deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k)
      =O[atTop] (fun t : ℝ => t ^ ((-s - 1).re + r)) := by
    refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) r _ ?_ ?_
      (by rw [← neg_re, neg_add'])
    · simpa [-neg_add_rev, neg_add'] using isBigO_deriv_ofReal_cpow_const_atTop (-s)
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans
        (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
  specialize hlim hboundary hderiv (integrableAtFilter_rpow_atTop_iff.mpr h₁)
  have hsum (n : ℕ) :
      ∑ k ∈ Icc 0 n, (k : ℂ) ^ (-s) * f k = ∑ k ∈ Icc 1 n, f k / (k : ℂ) ^ s := by
    rw [sum_Icc_zero_eq_sum_Icc_one (by simp [hf])]
    apply sum_congr rfl
    intro k hk
    rw [cpow_neg, div_eq_mul_inv, mul_comm]
  have hintegral :
      (0 : ℂ) - ∫ t in Set.Ioi (1 : ℝ),
        deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
    rw [zero_sub, ← integral_neg, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne', h₄]
    · ring_nf
    · exact neg_ne_zero.mpr h₂
  simpa only [Complex.ofReal_natCast, hsum, hintegral] using hlim

/-- Signed partial sums of size `O(N^r)` give ordered Dirichlet-series convergence
for `Re(s) > r`. No absolute-summability assumption is made. -/
theorem tendsto_dirichlet_sum_of_partialSums
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 1 n, f k / (k : ℂ) ^ s) atTop
      (𝓝 (s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))) := by
  let f₀ : ℕ → ℂ := fun n => if n = 0 then 0 else f n
  have hsum (n : ℕ) : ∑ k ∈ Icc 1 n, f₀ k = ∑ k ∈ Icc 1 n, f k := by
    apply sum_congr rfl
    intro k hk
    exact if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne'
  have hO₀ : (fun n : ℕ => ∑ k ∈ Icc 1 n, f₀ k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := hO.congr_left fun n => (hsum n).symm
  have hlim := tendsto_dirichlet_sum_of_partialSums_aux (by simp [f₀]) hr hs hO₀
  have hweight (n : ℕ) :
      ∑ k ∈ Icc 1 n, f₀ k / (k : ℂ) ^ s = ∑ k ∈ Icc 1 n, f k / (k : ℂ) ^ s := by
    apply sum_congr rfl
    intro k hk
    rw [show f₀ k = f k from if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']
  simpa only [hsum, hweight] using hlim

theorem norm_mellin_tail_le
    (M : ℝ → ℂ) {r C a : ℝ} (ha : 0 < a) {s : ℂ} (hs : r < s.re)
    (hM : ∀ t : ℝ, a < t → ‖M t‖ ≤ C * t ^ r) :
    ‖s * ∫ t in Set.Ioi a, M t * (t : ℂ) ^ (-(s + 1))‖ ≤
      C * ‖s‖ / (s.re - r) * a ^ (r - s.re) := by
  have hexp : r - s.re - 1 < -1 := by linarith
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi a),
      ‖M t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * t ^ (r - s.re - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ha.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, neg_re, add_re, one_re]
    calc
      ‖M t‖ * t ^ (-(s.re + 1)) ≤ (C * t ^ r) * t ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right (hM t ht) (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (r - s.re - 1) := by
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 2
        ring
  have hnorm := norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt hexp ha).const_mul C) hbound
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp ha] at hnorm
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_left hnorm (norm_nonneg s)).trans_eq ?_
  rw [show r - s.re - 1 + 1 = r - s.re by ring]
  have hden : s.re - r ≠ 0 := (sub_pos.mpr hs).ne'
  have hden' : r - s.re ≠ 0 := (sub_neg.mpr hs).ne
  field_simp [hden, hden']
  ring

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

theorem integrableOn_summatory_kernel {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) {s : ℂ} (hs : r < s.re) :
    IntegrableOn (fun t : ℝ => summatoryReal f t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have htop : summatoryReal f =O[atTop] (fun t : ℝ => t ^ (-(-r))) := by
    simpa using summatoryReal_isBigO_atTop hr hO
  have hconv := mellinConvergent_of_isBigO_rpow (s := -s)
    (locallyIntegrableOn_summatoryReal f) htop
    (by simp only [neg_re]; linarith) (summatoryReal_isBigO_atZero f (-s.re - 1))
    (by simp only [neg_re]; linarith)
  have hconv' := hconv.mono_set (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  convert hconv' using 1
  ext t
  simp only [smul_eq_mul]
  rw [show -(s + 1) = -s - 1 by ring, mul_comm]

theorem dirichlet_truncation_error_eq (f : ℕ → ℂ) (hf : f 0 = 0)
    {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) {s : ℂ} (hs : r < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    mellinExtension f s - (∑ k ∈ Icc 1 N, f k / (k : ℂ) ^ s) =
      -(N : ℂ) ^ (-s) * (∑ k ∈ Icc 1 N, f k) +
      s * ∫ t in Set.Ioi (N : ℝ), summatoryReal f t * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellinExtension, mellin_summatoryReal_neg_eq_integral,
    dirichlet_partialSum_eq f hf (hr.trans_lt hs)]
  have hint := intervalIntegral.integral_Ioi_sub_Ioi (b := (N : ℝ))
    (integrableOn_summatory_kernel hr hO hs) (by exact_mod_cast hN)
  rw [intervalIntegral.integral_of_le (by exact_mod_cast hN)] at hint
  rw [← hint]
  ring

theorem tendsto_dirichlet_sum_mellinExtension (f : ℕ → ℂ)
    {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 1 n, f k / (k : ℂ) ^ s)
      atTop (𝓝 (mellinExtension f s)) := by
  rw [mellinExtension, mellin_summatoryReal_neg_eq_integral]
  exact tendsto_dirichlet_sum_of_partialSums f hr hs hO

theorem summatoryReal_norm_le (f : ℕ → ℂ) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f k‖ ≤ C * (n : ℝ) ^ r)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖summatoryReal f t‖ ≤ C * t ^ r := by
  have hfloor : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  calc
    ‖summatoryReal f t‖ ≤ C * (⌊t⌋₊ : ℝ) ^ r := hbound _ hfloor
    _ ≤ C * t ^ r := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans ht)) hr) hC

/-- A quantitative remainder estimate for a Dirichlet series whose signed
partial sums satisfy the explicit bound `C * N^r`. -/
theorem dirichlet_truncation_error_le (f : ℕ → ℂ) (hf : f 0 = 0)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f k‖ ≤ C * (n : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖mellinExtension f s - (∑ k ∈ Icc 1 N, f k / (k : ℂ) ^ s)‖ ≤
      C * (1 + ‖s‖ / (s.re - r)) * (N : ℝ) ^ (r - s.re) := by
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
      using hbound n hn
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hpower : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hN0, neg_re]
  have hend : ‖-(N : ℂ) ^ (-s) * (∑ k ∈ Icc 1 N, f k)‖ ≤
      C * (N : ℝ) ^ (r - s.re) := by
    rw [norm_mul, norm_neg, hpower]
    calc
      (N : ℝ) ^ (-s.re) * ‖∑ k ∈ Icc 1 N, f k‖ ≤
          (N : ℝ) ^ (-s.re) * (C * (N : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left (hbound N hN) (Real.rpow_nonneg hN0.le _)
      _ = C * (N : ℝ) ^ (r - s.re) := by
        rw [mul_left_comm, ← Real.rpow_add hN0]
        congr 2
        ring
  have htail := norm_mellin_tail_le (summatoryReal f) hN0 hs
    (fun t ht => summatoryReal_norm_le f hr hC hbound (hNreal.trans ht.le))
  rw [dirichlet_truncation_error_eq f hf hr hO hs hN]
  refine (norm_add_le _ _).trans ((add_le_add hend htail).trans_eq ?_)
  ring

theorem tendstoUniformlyOn_dirichlet_bounded (f : ℕ → ℂ) (hf : f 0 = 0)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f k‖ ≤ C * (n : ℝ) ^ r)
    {σ R : ℝ} (hσ : r < σ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun N : ℕ => fun s : ℂ => ∑ k ∈ Icc 1 N, f k / (k : ℂ) ^ s)
      (mellinExtension f) atTop {s : ℂ | σ ≤ s.re ∧ ‖s‖ ≤ R} := by
  let D : ℝ := C * (1 + R / (σ - r))
  have hden : 0 < σ - r := sub_pos.mpr hσ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrate : Tendsto (fun N : ℕ => D * (N : ℝ) ^ (r - σ)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(σ - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hden).comp tendsto_natCast_atTop_atTop
    simpa only [neg_sub, mul_zero] using hpow.const_mul D
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hrate.eventually (eventually_lt_nhds hε), eventually_ge_atTop 1]
    with N hsmall hN
  intro s hs
  have hsr : r < s.re := hσ.trans_le hs.1
  have hsden : 0 < s.re - r := sub_pos.mpr hsr
  have hratio : ‖s‖ / (s.re - r) ≤ R / (σ - r) :=
    (div_le_div_of_nonneg_right hs.2 hsden.le).trans
      (div_le_div_of_nonneg_left hR hden (sub_le_sub_right hs.1 r))
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (r - s.re) ≤ (N : ℝ) ^ (r - σ) :=
    Real.rpow_le_rpow_of_exponent_le hNreal (sub_le_sub_left hs.1 r)
  rw [dist_eq_norm]
  refine (dirichlet_truncation_error_le f hf hr hC hbound hsr hN).trans_lt ?_
  apply lt_of_le_of_lt _ hsmall
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith :
      1 + ‖s‖ / (s.re - r) ≤ 1 + R / (σ - r)) hC)
    hpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hD

theorem tendstoLocallyUniformlyOn_dirichlet_of_bound (f : ℕ → ℂ) (hf : f 0 = 0)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f k‖ ≤ C * (n : ℝ) ^ r) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun s : ℂ => ∑ k ∈ Icc 1 N, f k / (k : ℂ) ^ s)
      (mellinExtension f) atTop {s : ℂ | r < s.re} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro s hs
  let σ : ℝ := (r + s.re) / 2
  let R : ℝ := ‖s‖ + 1
  have hσ : r < σ := by dsimp [σ]; change r < s.re at hs; linarith
  have hsσ : σ < s.re := by dsimp [σ]; change r < s.re at hs; linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨{z : ℂ | σ ≤ z.re ∧ ‖z‖ ≤ R}, ?_,
    tendstoUniformlyOn_dirichlet_bounded f hf hr hC hbound hσ hR⟩
  apply mem_nhdsWithin_of_mem_nhds
  have hRe : ∀ᶠ z : ℂ in 𝓝 s, σ < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsσ
  have hnorm : ∀ᶠ z : ℂ in 𝓝 s, ‖z‖ < R :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by dsimp [R]; linarith)
  filter_upwards [hRe, hnorm] with z hz hz'
  exact ⟨hz.le, hz'.le⟩

/-- The ordered Dirichlet series converges locally uniformly on `Re(s) > r`
under the ordinary signed partial-sum `O(N^r)` hypothesis. -/
theorem tendstoLocallyUniformlyOn_dirichlet_of_partialSums
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun s : ℂ => ∑ k ∈ Icc 1 N, f k / (k : ℂ) ^ s)
      (mellinExtension f) atTop {s : ℂ | r < s.re} := by
  let f₀ : ℕ → ℂ := fun n => if n = 0 then 0 else f n
  have hsum (n : ℕ) : ∑ k ∈ Icc 1 n, f₀ k = ∑ k ∈ Icc 1 n, f k := by
    apply sum_congr rfl
    intro k hk
    exact if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne'
  have hreal : summatoryReal f₀ = summatoryReal f := by
    funext t
    exact hsum ⌊t⌋₊
  have hF : mellinExtension f₀ = mellinExtension f := by
    funext s
    simp only [mellinExtension, hreal]
  obtain ⟨C, hC, hbound⟩ := bound_of_isBigO_nat_atTop hO
  have hbound₀ : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f₀ k‖ ≤ C * (n : ℝ) ^ r := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
    have hpow : (n : ℝ) ^ r ≠ 0 := (Real.rpow_pos_of_pos hn0 r).ne'
    simpa only [hsum, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0.le r)]
      using hbound hpow
  have hlocal := tendstoLocallyUniformlyOn_dirichlet_of_bound f₀ (by simp [f₀])
    hr hC.le hbound₀
  rw [hF] at hlocal
  apply hlocal.congr
  intro N s hs
  apply sum_congr rfl
  intro k hk
  rw [show f₀ k = f k from if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']

end RHMertens

end SourceOrdered

open MeasureTheory
open scoped Topology

theorem solution
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ r)) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)
      (fun s : ℂ => s * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-s))
      Filter.atTop {s : ℂ | r < s.re} := by
  exact RHMertens.tendstoLocallyUniformlyOn_dirichlet_of_partialSums f hr hO
