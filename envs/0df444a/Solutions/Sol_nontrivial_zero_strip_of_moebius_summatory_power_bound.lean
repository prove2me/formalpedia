-- Prove2me | solution 1 for nontrivial_zero_strip_of_moebius_summatory_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:46:29.560714+00:00
-- url     : https://prove2.me/submissions/8f3c728d-9486-4571-bf0f-2582fd4f9806

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform

section SourceZeta

open Complex Filter Set
open scoped Topology

namespace RHSketch

-- This entire function equals s * (1 - s) * zeta(s) away from 0 and 1.
noncomputable def regularizedZeta (s : ℂ) : ℂ :=
  (s * (1 - s) * completedRiemannZeta₀ s - 1) * (Gammaℝ s)⁻¹

lemma differentiable_regularizedZeta : Differentiable ℂ regularizedZeta := by
  exact (((differentiable_id.mul (differentiable_const 1 |>.sub differentiable_id)).mul
    differentiable_completedZeta₀).sub (differentiable_const 1)).mul
      differentiable_Gammaℝ_inv

lemma regularizedZeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    regularizedZeta s = s * (1 - s) * riemannZeta s := by
  rw [regularizedZeta, riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

theorem nonvanishing_of_moebius_extension
    (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re})
    (hmatch : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  let H : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hleft : AnalyticOnNhd ℂ (fun z => regularizedZeta z * F z) H :=
    (differentiable_regularizedZeta.differentiableOn.mul hF).analyticOnNhd hopen
  have hpoly : Differentiable ℂ (fun z : ℂ => z * (1 - z)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hright : AnalyticOnNhd ℂ (fun z : ℂ => z * (1 - z)) H :=
    hpoly.differentiableOn.analyticOnNhd hopen
  have hmatch' : (fun z => regularizedZeta z * F z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => z * (1 - z)) := by
    have hn : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      norm_num at hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    rw [regularizedZeta_eq hz0 hz1, hmatch z hz, mul_assoc]
    have hi := LSeries_one_mul_Lseries_moebius hz
    rw [LSeries_one_eq_riemannZeta hz] at hi
    rw [hi, mul_one]
  have heq : EqOn (fun z => regularizedZeta z * F z) (fun z => z * (1 - z)) H :=
    hleft.eqOn_of_preconnected_of_eventuallyEq hright
      (convex_halfSpace_re_gt (1 / 2)).isPreconnected (by norm_num [H]) hmatch'
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  intro hz
  have hid := heq hs
  dsimp only at hid
  rw [regularizedZeta_eq hs0 hs1, hz] at hid
  simp only [mul_zero, zero_mul] at hid
  exact (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))) hid.symm

theorem nontrivial_zero_reflect {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (h1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have h0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num [riemannZeta_zero] at hz
  have hg : Gammaℝ s ≠ 0 := by
    intro hg
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hg
    cases n with
    | zero => simp at hn; exact h0 hn
    | succ n =>
      apply hnt
      refine ⟨n, ?_⟩
      simpa [Nat.cast_add, Nat.cast_one, neg_mul] using hn
  have hc : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero h0, div_eq_zero_iff] at hz
    exact hz.resolve_right hg
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr (Ne.symm h1)),
    completedRiemannZeta_one_sub, hc, zero_div]

theorem nontrivial_zero_in_strip {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (h1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hs
    have hr := nontrivial_zero_reflect hz hnt h1
    apply riemannZeta_ne_zero_of_one_le_re (s := 1 - s) ?_ hr
    simp only [sub_re, one_re]
    linarith
  · by_contra hs
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hs) hz

theorem riemann_hypothesis_of_right_half_strip
    (hhalf : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2 := by
  intro s hz hnt h1
  obtain ⟨hl, hu⟩ := nontrivial_zero_in_strip hz hnt h1
  have hle : s.re ≤ 1 / 2 := by
    by_contra hs
    exact hhalf s (not_le.mp hs) hu hz
  have hge : 1 / 2 ≤ s.re := by
    by_contra hs
    have hlt : s.re < 1 / 2 := not_le.mp hs
    apply hhalf (1 - s) ?_ ?_ (nontrivial_zero_reflect hz hnt h1)
    · simp only [sub_re, one_re]
      linarith
    · simp only [sub_re, one_re]
      linarith
  exact le_antisymm hle hge

theorem riemann_hypothesis_of_moebius_extension
    (hext : ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s) :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2 := by
  obtain ⟨F, hF, hmatch⟩ := hext
  apply riemann_hypothesis_of_right_half_strip
  intro s hl hu
  apply nonvanishing_of_moebius_extension F hF hmatch hl
  intro hs
  subst s
  norm_num at hu

end RHSketch

end SourceZeta

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

section SourceStrip

open Complex Filter Set Asymptotics
open scoped Topology

namespace RHQuantitative

theorem nonvanishing_of_moebius_extension_halfplane
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | r < s.re})
    (hmatch : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s)
    {s : ℂ} (hs : r < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  let H : Set ℂ := {z : ℂ | r < z.re}
  have hopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hleft : AnalyticOnNhd ℂ (fun z => RHSketch.regularizedZeta z * F z) H :=
    (RHSketch.differentiable_regularizedZeta.differentiableOn.mul hF).analyticOnNhd hopen
  have hpoly : Differentiable ℂ (fun z : ℂ => z * (1 - z)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hright : AnalyticOnNhd ℂ (fun z : ℂ => z * (1 - z)) H :=
    hpoly.differentiableOn.analyticOnNhd hopen
  have hmatch' : (fun z => RHSketch.regularizedZeta z * F z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => z * (1 - z)) := by
    have hn : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      norm_num at hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    rw [RHSketch.regularizedZeta_eq hz0 hz1, hmatch z hz, mul_assoc]
    have hi := LSeries_one_mul_Lseries_moebius hz
    rw [LSeries_one_eq_riemannZeta hz] at hi
    rw [hi, mul_one]
  have htwo : (2 : ℂ) ∈ H := by
    norm_num [H]
    linarith
  have heq : EqOn (fun z => RHSketch.regularizedZeta z * F z)
      (fun z => z * (1 - z)) H :=
    hleft.eqOn_of_preconnected_of_eventuallyEq hright
      (convex_halfSpace_re_gt r).isPreconnected htwo hmatch'
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  intro hz
  have hid := heq hs
  dsimp only at hid
  rw [RHSketch.regularizedZeta_eq hs0 hs1, hz] at hid
  simp only [mul_zero, zero_mul] at hid
  exact (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))) hid.symm

theorem nonvanishing_of_mertens_power_bound
    {r : ℝ} (hr : 0 ≤ r)
    (hM : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hs : r < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  by_cases hr1 : r < 1
  · apply nonvanishing_of_moebius_extension_halfplane hr hr1
      (RHMertens.mellinExtension (fun n => (ArithmeticFunction.moebius n : ℂ)))
      ?_ ?_ hs hs1
    · intro z hz
      exact (RHMertens.differentiableAt_mellinExtension_of_partialSums hr hM
        hz).differentiableWithinAt
    · intro z hz
      exact RHMertens.mellinExtension_eq_LSeries _ hr (hr1.trans hz)
        (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hz) hM
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)

theorem nontrivial_zero_strip_of_mertens_power_bound
    {r : ℝ} (hr : 0 ≤ r)
    (hM : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (h1 : s ≠ 1) :
    1 - r ≤ s.re ∧ s.re ≤ r := by
  have hstrip := RHSketch.nontrivial_zero_in_strip hz hnt h1
  constructor
  · by_contra h
    have hreflect : riemannZeta (1 - s) = 0 :=
      RHSketch.nontrivial_zero_reflect hz hnt h1
    have hreflect_re : r < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    have hreflect_ne_one : 1 - s ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp only [sub_re, one_re] at hre
      linarith [hstrip.1]
    exact nonvanishing_of_mertens_power_bound hr hM hreflect_re
      hreflect_ne_one hreflect
  · by_contra h
    exact nonvanishing_of_mertens_power_bound hr hM (not_le.mp h) h1 hz

theorem riemannHypothesis_of_mertens_power_bound
    {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hM : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r)) :
    RiemannHypothesis := by
  intro s hz hnt h1
  obtain ⟨hl, hu⟩ := nontrivial_zero_strip_of_mertens_power_bound hr hM hz hnt h1
  linarith

end RHQuantitative

end SourceStrip

open MeasureTheory
open scoped Topology

theorem solution
    {r : ℝ} (hr : 0 ≤ r)
    (hM : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (h1 : s ≠ 1) :
    1 - r ≤ s.re ∧ s.re ≤ r := by
  exact RHQuantitative.nontrivial_zero_strip_of_mertens_power_bound hr hM hz hnt h1
