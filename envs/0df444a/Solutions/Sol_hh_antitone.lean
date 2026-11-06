-- Prove2me | solution 1 for hh_antitone
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:31:31.394995+00:00
-- url     : https://prove2.me/submissions/278f45f0-f4e4-4a5c-8c8a-b53fc63b8442

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Definitions.Def_PrimeNumberTheoremAnd_SmoothExistence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
attribute [fun_prop] Real.continuous_fourierChar
attribute [fun_prop] measurable_coe_nnreal_ennreal

private lemma pp_pos_aux {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

private lemma hh_deriv_aux (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 :=
    mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert l4.pow 2 using 1 <;> first | rfl | ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert (hasDerivAt_id' t).mul l2 using 1 <;>
      first | rfl | (field_simp [ht]; ring)
  apply (l1.inv e1).congr_deriv
  dsimp only [hh', pp, hh]
  simp only [div_eq_mul_inv, inv_pow]
  ring

private lemma hh_continuous_aux (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv_aux a ht.ne.symm).continuousAt.continuousWithinAt

private lemma hh'_nonpos_aux {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos_aux ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

theorem solution {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv_aux a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous_aux _) l1
    (fun x _ => hh'_nonpos_aux ha)
