-- Prove2me | solution 1 for riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:21:07.824618+00:00
-- url     : https://prove2.me/submissions/3925d32a-158a-49f6-81c3-0db286a5d066
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_dirichlet_series_holomorphic_extension
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

-- The imported extension-existence conjecture is the only open child.
theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re = 1 / 2 := by
  exact RHSketch.riemann_hypothesis_of_moebius_extension
    moebius_dirichlet_series_holomorphic_extension
