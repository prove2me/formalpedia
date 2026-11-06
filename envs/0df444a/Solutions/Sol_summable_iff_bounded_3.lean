-- Prove2me | solution 3 for summable_iff_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:36.554486+00:00
-- url     : https://prove2.me/submissions/ab178c5d-c227-405a-9d11-f864056003eb

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

theorem solution {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  constructor
  · intro h
    refine Asymptotics.IsBigO.of_bound (∑' i, u i) (Filter.Eventually.of_forall fun n => ?_)
    have h1 : 0 ≤ cumsum u n := Finset.sum_nonneg fun i _ => hu i
    have h2 : cumsum u n ≤ ∑' i, u i := h.sum_le_tsum _ (fun i _ => hu i)
    simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2
  · intro h
    obtain ⟨c, hc⟩ := h.bound
    rw [Filter.eventually_atTop] at hc
    obtain ⟨N, hN⟩ := hc
    apply summable_of_sum_range_le (c := max c (cumsum u N)) hu
    intro n
    by_cases hn : N ≤ n
    · have := hN n hn
      simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    · push Not at hn
      refine le_trans ?_ (le_max_right _ _)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hn.le) (fun i _ _ => hu i)
