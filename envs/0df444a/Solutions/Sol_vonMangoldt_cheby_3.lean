-- Prove2me | solution 3 for vonMangoldt_cheby
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:44.770095+00:00
-- url     : https://prove2.me/submissions/e88a1d04-1b5c-42d3-9712-2016f3ea76e7

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
attribute [local instance] _p2m_local_instance_2ee1fa6ce2_1687

theorem solution : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(Λ k : ℂ)‖) n ≤ C * n) := by
  refine ⟨Real.log 4 + 4, fun n => ?_⟩
  have h := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (Nat.cast_nonneg n)
  have h2 : cumsum (fun k : ℕ ↦ ‖(Λ k : ℂ)‖) n ≤ Chebyshev.psi n := by
    unfold cumsum
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    have e : ∀ k, ‖(Λ k : ℂ)‖ = Λ k := fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simp only [e]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by simp at hk ⊢ <;> omega)
      (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  exact h2.trans h
