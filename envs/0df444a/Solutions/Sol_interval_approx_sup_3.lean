-- Prove2me | solution 3 for interval_approx_sup
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:46.418+00:00
-- url     : https://prove2.me/submissions/bf9c52b7-4d08-4de2-ad86-89193ec32a5d

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

theorem solution (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by
  have hmem : Ioo (0:ℝ) (2 * a) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by linarith)
  filter_upwards [hmem] with ε hε
  rcases hε with ⟨hε1, hε2⟩
  let bump : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 2, (b - a) / 2 + ε / 2, by linarith, by linarith⟩
  have hrO : bump.rOut = (b - a) / 2 + ε / 2 := rfl
  have hrI : bump.rIn = (b - a) / 2 := rfl
  have hcont : Continuous (bump : ℝ → ℝ) := bump.continuous
  have hcs : HasCompactSupport (bump : ℝ → ℝ) := bump.hasCompactSupport
  refine ⟨bump, bump.contDiff, hcs, ?_, ?_, ?_⟩
  · show tsupport (bump : ℝ → ℝ) ⊆ _
    rw [bump.tsupport_eq]
    intro y hy
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrO] at hy
    simp only [mem_Ioi]
    linarith [hy.1]
  · intro y
    by_cases hy : y ∈ Ico a b
    · have : y ∈ Metric.closedBall ((a + b) / 2) bump.rIn := by
        rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrI]
        constructor <;> linarith [hy.1, hy.2]
      rw [bump.one_of_mem_closedBall this]
      simp [hy]
    · simp only [indicator_of_notMem hy]
      exact bump.nonneg'  y
  · have hint : Integrable (bump : ℝ → ℝ) := hcont.integrable_of_hasCompactSupport hcs
    calc ∫ y in Ioi 0, bump y ≤ ∫ y, bump y :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall fun y => bump.nonneg' y)
      _ = ∫ y in Metric.closedBall ((a + b) / 2) bump.rOut, bump y := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro y hy
          exact bump.zero_of_le_dist (by
            rw [Metric.mem_closedBall, not_le] at hy
            exact hy.le)
      _ ≤ ∫ y in Metric.closedBall ((a + b) / 2) bump.rOut, (1 : ℝ) := by
          apply setIntegral_mono_on hint.integrableOn _ measurableSet_closedBall
          · intro y _; exact bump.le_one
          · exact integrableOn_const measure_closedBall_lt_top.ne
      _ = b - a + ε := by
          rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_closedBall,
            hrO, ENNReal.toReal_ofReal (by linarith)]
          ring
