-- Prove2me | solution 1 for dirichlet_mellin_logarithmic_moments_and_all_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:49:41.138243+00:00
-- url     : https://prove2.me/submissions/b40b7e25-aaf1-4a15-9468-c74df08e7193

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Linarith
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

section SourceMoments

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHMertens

noncomputable def logarithmicSummatory (f : ℕ → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (Real.log t) ^ k • summatoryReal f t

noncomputable def mellinMoment (f : ℕ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  mellin (logarithmicSummatory f k) (-s)

lemma logarithmicSummatory_succ (f : ℕ → ℂ) (k : ℕ) (t : ℝ) :
    logarithmicSummatory f (k + 1) t = Real.log t • logarithmicSummatory f k t := by
  simp only [logarithmicSummatory, pow_succ, mul_comm, mul_smul]

lemma locallyIntegrableOn_logarithmicSummatory (f : ℕ → ℂ) (k : ℕ) :
    LocallyIntegrableOn (logarithmicSummatory f k) (Ioi 0) := by
  apply (locallyIntegrableOn_summatoryReal f).continuousOn_smul isOpen_Ioi.isLocallyClosed
  exact (Real.continuousOn_log.mono
    (subset_compl_singleton_iff.mpr self_notMem_Ioi)).pow k

lemma logarithmicSummatory_isBigO_atTop
    {f : ℕ → ℂ} {r q : ℝ} (hr : 0 ≤ r)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r)) (hq : r < q) (k : ℕ) :
    logarithmicSummatory f k =O[atTop] (fun t : ℝ => t ^ q) := by
  have hlog : (fun t : ℝ => (Real.log t) ^ k) =O[atTop]
      (fun t : ℝ => t ^ (q - r)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (sub_pos.mpr hq)).isBigO
  refine (hlog.smul (summatoryReal_isBigO_atTop hr hO)).congr' .rfl ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [smul_eq_mul, ← Real.rpow_add ht, sub_add_cancel]

lemma logarithmicSummatory_isBigO_atZero (f : ℕ → ℂ) (k : ℕ) (b : ℝ) :
    logarithmicSummatory f k =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] 0] logarithmicSummatory f k := by
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with t ht
    simp [logarithmicSummatory, summatoryReal_eq_zero ht]
  exact (isBigO_zero (fun t : ℝ => t ^ (-b)) (𝓝[>] 0)).congr' heq .rfl

theorem mellinMoment_convergent_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r))
    (k : ℕ) {s : ℂ} (hs : r < s.re) :
    MellinConvergent (logarithmicSummatory f k) (-s) := by
  have htop : logarithmicSummatory f k =O[atTop]
      (fun t : ℝ => t ^ (-(-((r + s.re) / 2)))) := by
    simpa using logarithmicSummatory_isBigO_atTop hr hO
      (by linarith : r < (r + s.re) / 2) k
  exact mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_logarithmicSummatory f k)
    htop (by simp only [neg_re]; linarith)
    (logarithmicSummatory_isBigO_atZero f k (-s.re - 1))
    (by simp only [neg_re]; linarith)

theorem hasDerivAt_mellinMoment_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r))
    (k : ℕ) {s : ℂ} (hs : r < s.re) :
    HasDerivAt (mellinMoment f k) (-mellinMoment f (k + 1) s) s := by
  have htop : logarithmicSummatory f k =O[atTop]
      (fun t : ℝ => t ^ (-(-((r + s.re) / 2)))) := by
    simpa using logarithmicSummatory_isBigO_atTop hr hO
      (by linarith : r < (r + s.re) / 2) k
  have hd := (mellin_hasDerivAt_of_isBigO_rpow
    (locallyIntegrableOn_logarithmicSummatory f k)
    htop (by simp only [neg_re]; linarith : (-s).re < -((r + s.re) / 2))
    (logarithmicSummatory_isBigO_atZero f k (-s.re - 1))
    (by simp only [neg_re]; linarith : -s.re - 1 < (-s).re)).2
  have heq : logarithmicSummatory f (k + 1) =
      (fun t => Real.log t • logarithmicSummatory f k t) :=
    funext (logarithmicSummatory_succ f k)
  change HasDerivAt (fun z => mellin (logarithmicSummatory f k) (-z))
    (-mellin (logarithmicSummatory f (k + 1)) (-s)) s
  rw [heq]
  simpa only [Function.comp_def, mul_neg, mul_one] using!
    hd.comp s (hasDerivAt_id s).neg

theorem deriv_mellinMoment_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r))
    (k : ℕ) {s : ℂ} (hs : r < s.re) :
    deriv (mellinMoment f k) s = -mellinMoment f (k + 1) s :=
  (hasDerivAt_mellinMoment_of_partialSums hr hO k hs).deriv

theorem analyticOnNhd_mellinMoment_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r)) (k : ℕ) :
    AnalyticOnNhd ℂ (mellinMoment f k) {s : ℂ | r < s.re} := by
  have hopen : IsOpen {s : ℂ | r < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro s hs
  exact (hasDerivAt_mellinMoment_of_partialSums hr hO k hs).differentiableAt.differentiableWithinAt

theorem iteratedDeriv_mellinMoment_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r)) (k n : ℕ)
    {s : ℂ} (hs : r < s.re) :
    iteratedDeriv n (mellinMoment f k) s = (-1 : ℂ) ^ n * mellinMoment f (k + n) s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hd := (hasDerivAt_mellinMoment_of_partialSums hr hO (k + n) hs).const_mul
      ((-1 : ℂ) ^ n)
    have heq : iteratedDeriv n (mellinMoment f k) =ᶠ[𝓝 s]
        (fun z => (-1 : ℂ) ^ n * mellinMoment f (k + n) z) := by
      have hn : {z : ℂ | r < z.re} ∈ 𝓝 s :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
      filter_upwards [hn] with z hz
      exact ih hz
    have hid := (hd.congr_of_eventuallyEq heq).deriv
    convert! hid using 1
    simp [pow_succ, Nat.add_assoc]

end RHMertens


namespace RHMertens

theorem iteratedDeriv_succ_mellinExtension_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r)) (n : ℕ)
    {s : ℂ} (hs : r < s.re) :
    iteratedDeriv (n + 1) (mellinExtension f) s =
      (-1 : ℂ) ^ (n + 1) * s * mellinMoment f (n + 1) s +
        ((n + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ n * mellinMoment f n s := by
  induction n generalizing s with
  | zero =>
    have hzero : logarithmicSummatory f 0 = summatoryReal f := by
      funext t
      simp [logarithmicSummatory]
    have hF := (hasDerivAt_id s).mul (hasDerivAt_mellinMoment_of_partialSums hr hO 0 hs)
    rw [iteratedDeriv_one]
    convert! hF.deriv using 1
    · congr 1
      ext z
      simp [mellinExtension, mellinMoment, hzero]
    · simp
      ring
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hA := ((hasDerivAt_id s).const_mul ((-1 : ℂ) ^ (n + 1))).mul
      (hasDerivAt_mellinMoment_of_partialSums hr hO (n + 1) hs)
    have hB := (hasDerivAt_mellinMoment_of_partialSums hr hO n hs).const_mul
      (((n + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ n)
    have heq : iteratedDeriv (n + 1) (mellinExtension f) =ᶠ[𝓝 s]
        (fun z => (-1 : ℂ) ^ (n + 1) * z * mellinMoment f (n + 1) z +
          ((n + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ n * mellinMoment f n z) := by
      have hn : {z : ℂ | r < z.re} ∈ 𝓝 s :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
      filter_upwards [hn] with z hz
      exact ih hz
    have hderiv := ((hA.add hB).congr_of_eventuallyEq heq).deriv
    convert! hderiv using 1
    simp only [Nat.cast_add, Nat.cast_one, pow_succ, id_eq]
    ring

end RHMertens

end SourceMoments

open MeasureTheory
open scoped Topology

theorem solution
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hs : r < s.re) :
    let M := fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n
    let J := fun k : ℕ => fun z : ℂ => mellin (fun t => (Real.log t) ^ k • M t) (-z)
    let F := fun z : ℂ => z * mellin M (-z)
    (∀ k : ℕ, MellinConvergent (fun t => (Real.log t) ^ k • M t) (-s)) ∧
    (∀ k n : ℕ, iteratedDeriv n (J k) s = (-1 : ℂ) ^ n * J (k + n) s) ∧
    (∀ n : ℕ, iteratedDeriv (n + 1) F s =
      (-1 : ℂ) ^ (n + 1) * s * J (n + 1) s +
        ((n + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ n * J n s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact RHMertens.mellinMoment_convergent_of_partialSums hr hO k hs
  · intro k n
    exact RHMertens.iteratedDeriv_mellinMoment_of_partialSums hr hO k n hs
  · intro n
    exact RHMertens.iteratedDeriv_succ_mellinExtension_of_partialSums hr hO n hs
