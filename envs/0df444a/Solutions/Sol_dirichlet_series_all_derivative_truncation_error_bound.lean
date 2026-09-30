-- Prove2me | solution 1 for dirichlet_series_all_derivative_truncation_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:13:04.047847+00:00
-- url     : https://prove2.me/submissions/01348e78-ffc9-4943-87a6-0baecc037f71

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

set_option autoImplicit false

open Complex Filter MeasureTheory Asymptotics
open scoped Topology

namespace DerivativeDirichlet3df

open Set

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

end DerivativeDirichlet3df

open Finset Filter MeasureTheory Complex Asymptotics

namespace DerivativeDirichlet3df

private lemma sum_Icc_zero_eq_sum_Icc_one {f : ℕ → ℂ} (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := by
  rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp), hf, zero_add,
    zero_add]

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

noncomputable def logWeightedPartialSum (f : ℕ → ℂ) (j N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Icc 1 N, f k * (-Complex.log (k : ℂ)) ^ j / (k : ℂ) ^ s

lemma hasDerivAt_dirichletTerm (c : ℂ) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    HasDerivAt (fun z : ℂ => c / (n : ℂ) ^ z)
      (c * (-Complex.log (n : ℂ)) / (n : ℂ) ^ s) s := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := ((hasDerivAt_id s).neg.const_cpow (c := (n : ℂ)) (Or.inl hn')).const_mul c
  simp only [Pi.neg_apply, id_eq] at h
  convert! h using 1
  · ext z
    rw [cpow_neg, div_eq_mul_inv]
  · rw [cpow_neg, div_eq_mul_inv]
    ring

lemma hasDerivAt_logWeightedPartialSum (f : ℕ → ℂ) (j N : ℕ) (s : ℂ) :
    HasDerivAt (logWeightedPartialSum f j N) (logWeightedPartialSum f (j + 1) N s) s := by
  unfold logWeightedPartialSum
  have hterm : ∀ k ∈ Icc 1 N,
      HasDerivAt
        (fun z : ℂ => f k * (-Complex.log (k : ℂ)) ^ j / (k : ℂ) ^ z)
        (f k * (-Complex.log (k : ℂ)) ^ (j + 1) / (k : ℂ) ^ s) s := by
    intro k hk
    convert hasDerivAt_dirichletTerm (f k * (-Complex.log (k : ℂ)) ^ j)
      (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne' s using 1
    rw [pow_succ]
    ring
  exact HasDerivAt.fun_sum hterm

end DerivativeDirichlet3df

open Finset Filter Complex Asymptotics Metric
open scoped Topology

namespace DerivativeDirichlet3df

lemma iteratedDeriv_logWeightedPartialSum (f : ℕ → ℂ) (N j : ℕ) :
    iteratedDeriv j (logWeightedPartialSum f 0 N) = logWeightedPartialSum f j N := by
  induction j with
  | zero => exact iteratedDeriv_zero
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (hasDerivAt_logWeightedPartialSum f j N s).deriv

/-- Cauchy's estimate converts the zeroth-order Dirichlet truncation bound
on a disk into an explicit bound for every logarithm-weighted derivative. -/
theorem dirichlet_derivative_truncation_error_le_of_zero (f : ℕ → ℂ) (hf : f 0 = 0)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f k‖ ≤ C * (n : ℝ) ^ r)
    {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδgap : δ < s.re - r)
    {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    ‖iteratedDeriv j (mellinExtension f) s - logWeightedPartialSum f j N s‖ ≤
      (j.factorial : ℝ) / δ ^ j * C *
        (1 + (‖s‖ + δ) / (s.re - δ - r)) * (N : ℝ) ^ (r - s.re + δ) := by
  have hs : r < s.re := by linarith
  have hden : 0 < s.re - δ - r := by linarith
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
      using hbound n hn
  have hF : DifferentiableOn ℂ (mellinExtension f) {z : ℂ | r < z.re} :=
    fun z hz => (differentiableAt_mellinExtension_of_partialSums hr hO hz).differentiableWithinAt
  have hP : Differentiable ℂ (logWeightedPartialSum f 0 N) :=
    fun z => (hasDerivAt_logWeightedPartialSum f 0 N z).differentiableAt
  have hopen : IsOpen {z : ℂ | r < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hclosed : closedBall s δ ⊆ {z : ℂ | r < z.re} := by
    intro z hz
    have hnorm : ‖s - z‖ ≤ δ := by
      rw [norm_sub_rev]
      exact mem_closedBall_iff_norm.mp hz
    have hre := (Complex.re_le_norm (s - z)).trans hnorm
    rw [sub_re] at hre
    change r < z.re
    linarith
  let E : ℂ → ℂ := fun z => mellinExtension f z - logWeightedPartialSum f 0 N z
  have hE : DiffContOnCl ℂ E (ball s δ) :=
    (hF.sub hP.differentiableOn).diffContOnCl_ball hclosed
  let B : ℝ := C * (1 + (‖s‖ + δ) / (s.re - δ - r)) * (N : ℝ) ^ (r - s.re + δ)
  have hB : ∀ z ∈ sphere s δ, ‖E z‖ ≤ B := by
    intro z hz
    have hdist : ‖z - s‖ = δ := mem_sphere_iff_norm.mp hz
    have hzre : s.re - δ ≤ z.re := by
      have hre := Complex.re_le_norm (s - z)
      rw [sub_re, norm_sub_rev, hdist] at hre
      linarith
    have hznorm : ‖z‖ ≤ ‖s‖ + δ := by
      calc
        ‖z‖ = ‖(z - s) + s‖ := by congr 1; ring
        _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
        _ = ‖s‖ + δ := by rw [hdist]; ring
    have hzr : r < z.re := by linarith
    have hzden : 0 < z.re - r := sub_pos.mpr hzr
    have hratio : ‖z‖ / (z.re - r) ≤ (‖s‖ + δ) / (s.re - δ - r) :=
      (div_le_div_of_nonneg_right hznorm hzden.le).trans
        (div_le_div_of_nonneg_left (by positivity) hden (by linarith))
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpow : (N : ℝ) ^ (r - z.re) ≤ (N : ℝ) ^ (r - s.re + δ) :=
      Real.rpow_le_rpow_of_exponent_le hNreal (by linarith)
    have hbase : ‖E z‖ ≤ C * (1 + ‖z‖ / (z.re - r)) * (N : ℝ) ^ (r - z.re) := by
      simpa only [E, logWeightedPartialSum, pow_zero, mul_one]
        using dirichlet_truncation_error_le f hf hr hC hbound hzr hN
    refine hbase.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith :
        1 + ‖z‖ / (z.re - r) ≤ 1 + (‖s‖ + δ) / (s.re - δ - r)) hC)
      hpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by positivity)
  have hderiv : iteratedDeriv j E s =
      iteratedDeriv j (mellinExtension f) s - logWeightedPartialSum f j N s := by
    dsimp only [E]
    rw [iteratedDeriv_fun_sub (hF.analyticAt (hopen.mem_nhds hs)).contDiffAt
      (hP.analyticAt s).contDiffAt, iteratedDeriv_logWeightedPartialSum]
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hδ hE hB
  rw [hderiv] at hcauchy
  refine hcauchy.trans_eq ?_
  dsimp only [B]
  simp only [div_eq_mul_inv]
  ring

/-- Quantitative approximation of every derivative of the Dirichlet continuation.
The coefficient at zero is irrelevant; all finite sums begin at one. -/
theorem dirichlet_derivative_truncation_error_le (f : ℕ → ℂ)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f k‖ ≤ C * (n : ℝ) ^ r)
    {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδgap : δ < s.re - r)
    {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    ‖iteratedDeriv j (mellinExtension f) s - logWeightedPartialSum f j N s‖ ≤
      (j.factorial : ℝ) / δ ^ j * C *
        (1 + (‖s‖ + δ) / (s.re - δ - r)) * (N : ℝ) ^ (r - s.re + δ) := by
  let f₀ : ℕ → ℂ := fun n => if n = 0 then 0 else f n
  have hsum (n : ℕ) : ∑ k ∈ Icc 1 n, f₀ k = ∑ k ∈ Icc 1 n, f k := by
    apply sum_congr rfl
    intro k hk
    exact if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne'
  have hreal : summatoryReal f₀ = summatoryReal f := by
    funext t
    exact hsum ⌊t⌋₊
  have hF : mellinExtension f₀ = mellinExtension f := by
    funext z
    simp only [mellinExtension, hreal]
  have hlog : logWeightedPartialSum f₀ j N = logWeightedPartialSum f j N := by
    funext z
    unfold logWeightedPartialSum
    apply sum_congr rfl
    intro k hk
    rw [show f₀ k = f k from if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']
  have hbound₀ : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f₀ k‖ ≤ C * (n : ℝ) ^ r := by
    intro n hn
    rw [hsum]
    exact hbound n hn
  have herror := dirichlet_derivative_truncation_error_le_of_zero f₀ (by simp [f₀])
    hr hC hbound₀ hδ hδgap hN j
  simpa only [hF, hlog] using herror

end DerivativeDirichlet3df

theorem solution
    (f : ℕ → ℂ) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ C * (N : ℝ) ^ r)
    {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδgap : δ < s.re - r)
    {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    ‖iteratedDeriv j (fun z : ℂ =>
        z * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-z)) s -
      (∑ n ∈ Finset.Icc 1 N, f n * (-Complex.log (n : ℂ)) ^ j / (n : ℂ) ^ s)‖ ≤
      (j.factorial : ℝ) / δ ^ j * C *
        (1 + (‖s‖ + δ) / (s.re - δ - r)) * (N : ℝ) ^ (r - s.re + δ) := by
  have hF : DerivativeDirichlet3df.mellinExtension f = (fun z : ℂ =>
      z * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-z)) := rfl
  simpa only [hF, DerivativeDirichlet3df.logWeightedPartialSum] using
    DerivativeDirichlet3df.dirichlet_derivative_truncation_error_le f hr hC hbound hδ hδgap hN j

#print axioms solution
