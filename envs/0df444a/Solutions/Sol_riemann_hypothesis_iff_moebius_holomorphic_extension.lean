-- Prove2me | solution 1 for riemann_hypothesis_iff_moebius_holomorphic_extension
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:46:28.280092+00:00
-- url     : https://prove2.me/submissions/8ab03183-338f-415d-8716-d5eb66b71155

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

section SourceConverse

open Complex

namespace RHConverse

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

lemma regularizedZeta_one : regularizedZeta 1 = -1 := by
  simp [regularizedZeta, Gammaℝ_one]

noncomputable def reciprocalZeta (s : ℂ) : ℂ :=
  s * (1 - s) / regularizedZeta s

lemma reciprocalZeta_one : reciprocalZeta 1 = 0 := by
  simp [reciprocalZeta]

lemma hasDerivAt_reciprocalZeta_one : HasDerivAt reciprocalZeta 1 1 := by
  have hnum : HasDerivAt (fun z : ℂ ↦ z * (1 - z)) (-1) 1 := by
    convert! (hasDerivAt_id (1 : ℂ)).mul
      ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (1 : ℂ))) using 1
    norm_num
  have hden := (differentiable_regularizedZeta (1 : ℂ)).hasDerivAt
  have hne : regularizedZeta 1 ≠ 0 := by rw [regularizedZeta_one]; norm_num
  simpa [reciprocalZeta, regularizedZeta_one] using! hnum.div hden hne

lemma deriv_reciprocalZeta_one : deriv reciprocalZeta 1 = 1 :=
  hasDerivAt_reciprocalZeta_one.deriv

lemma zeta_nonzero_of_riemann_hypothesis (hRH : RiemannHypothesis)
    {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero
  intro hz
  have hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num [mul_re] at hs
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have heq := hRH s hz hnt hs1
  linarith

lemma regularizedZeta_nonzero_of_riemann_hypothesis (hRH : RiemannHypothesis)
    {s : ℂ} (hs : 1 / 2 < s.re) : regularizedZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [regularizedZeta_one]
    norm_num
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  rw [regularizedZeta_eq hs0 hs1]
  exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1)))
    (zeta_nonzero_of_riemann_hypothesis hRH hs)

theorem differentiableOn_reciprocalZeta_of_riemann_hypothesis (hRH : RiemannHypothesis) :
    DifferentiableOn ℂ reciprocalZeta {s : ℂ | 1 / 2 < s.re} := by
  have hnum : Differentiable ℂ (fun s : ℂ ↦ s * (1 - s)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  exact hnum.differentiableOn.div differentiable_regularizedZeta.differentiableOn
    (fun s hs ↦ regularizedZeta_nonzero_of_riemann_hypothesis hRH hs)

theorem reciprocalZeta_eq_moebius_LSeries {s : ℂ} (hs : 1 < s.re) :
    reciprocalZeta s =
      LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hpoly : s * (1 - s) ≠ 0 :=
    mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hi := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hi
  rw [reciprocalZeta, regularizedZeta_eq hs0 hs1]
  apply (div_eq_iff (mul_ne_zero hpoly hz)).2
  calc
    s * (1 - s) = (s * (1 - s)) *
        (riemannZeta s * LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s) := by
      rw [hi, mul_one]
    _ = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s *
        (s * (1 - s) * riemannZeta s) := by ring

theorem moebius_extension_of_riemann_hypothesis (hRH : RiemannHypothesis) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s := by
  exact ⟨reciprocalZeta, differentiableOn_reciprocalZeta_of_riemann_hypothesis hRH,
    fun s hs ↦ reciprocalZeta_eq_moebius_LSeries hs⟩

theorem normalized_moebius_extension_of_riemann_hypothesis (hRH : RiemannHypothesis) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s) ∧
      F 1 = 0 ∧ HasDerivAt F 1 1 := by
  exact ⟨reciprocalZeta, differentiableOn_reciprocalZeta_of_riemann_hypothesis hRH,
    fun s hs ↦ reciprocalZeta_eq_moebius_LSeries hs,
    reciprocalZeta_one, hasDerivAt_reciprocalZeta_one⟩


end RHConverse

end SourceConverse

section SourceUniqueness

open Complex Filter Set
open scoped Topology

namespace RHConverse

theorem moebius_extension_unique
    (F G : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re})
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hmatchF : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s)
    (hmatchG : ∀ s : ℂ, 1 < s.re →
      G s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s) :
    EqOn F G {s : ℂ | 1 / 2 < s.re} := by
  let H : Set ℂ := {s : ℂ | 1 / 2 < s.re}
  have hopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hnear : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hright : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hright] with s hs
    rw [hmatchF s hs, hmatchG s hs]
  exact (hF.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hopen) (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (by norm_num [H]) hnear

theorem moebius_extension_eq_canonical_and_normalized
    (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re})
    (hmatch : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s) :
    EqOn F reciprocalZeta {s : ℂ | 1 / 2 < s.re} ∧
      F 1 = 0 ∧ HasDerivAt F 1 1 := by
  have hRH : RiemannHypothesis :=
    RHSketch.riemann_hypothesis_of_moebius_extension ⟨F, hF, hmatch⟩
  have heq : EqOn F reciprocalZeta {s : ℂ | 1 / 2 < s.re} :=
    moebius_extension_unique F reciprocalZeta hF
      (differentiableOn_reciprocalZeta_of_riemann_hypothesis hRH)
      hmatch (fun s hs ↦ reciprocalZeta_eq_moebius_LSeries hs)
  have hnear : F =ᶠ[𝓝 (1 : ℂ)] reciprocalZeta := by
    have hhalf : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hhalf] with s hs using heq hs
  refine ⟨heq, ?_, hasDerivAt_reciprocalZeta_one.congr_of_eventuallyEq hnear⟩
  rw [heq (by norm_num : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re}), reciprocalZeta_one]

theorem moebius_extension_deriv_one
    (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re})
    (hmatch : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s) :
    deriv F 1 = 1 :=
  (moebius_extension_eq_canonical_and_normalized F hF hmatch).2.2.deriv

theorem riemannHypothesis_iff_moebius_extension :
    RiemannHypothesis ↔
      ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
        ∀ s : ℂ, 1 < s.re →
          F s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s := by
  exact ⟨moebius_extension_of_riemann_hypothesis,
    RHSketch.riemann_hypothesis_of_moebius_extension⟩

theorem riemannHypothesis_iff_normalized_moebius_extension :
    RiemannHypothesis ↔
      ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 < s.re →
          F s = LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s) ∧
        F 1 = 0 ∧ HasDerivAt F 1 1 := by
  constructor
  · exact normalized_moebius_extension_of_riemann_hypothesis
  · rintro ⟨F, hF, hmatch, _, _⟩
    exact RHSketch.riemann_hypothesis_of_moebius_extension ⟨F, hF, hmatch⟩


end RHConverse

end SourceUniqueness

open MeasureTheory
open scoped Topology

theorem solution :
    RiemannHypothesis ↔
      ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
        ∀ s : ℂ, 1 < s.re →
          F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s := by
  exact RHConverse.riemannHypothesis_iff_moebius_extension
