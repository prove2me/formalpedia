-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_generator_q_harmonic_of_pointwise_jet_and_jump_limit
-- name    : AvramDividend.Classical.avram_wave4_01_generator_q_harmonic_of_pointwise_jet_and_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:47:19.870474+00:00
-- url     : https://prove2.me/theorems/70eafb57-6585-4091-ad55-2a55161943b4
-- title:
--   Exact compensated Lévy generator q-harmonicity passes to limits of values, derivative jets and full nonlocal jump integrals
-- statement:
--   Fix the true spectrally negative Lévy generator Γ and a spatial point x. Suppose f lies in the actual generator jump-integrability domain, and q-harmonic approximants f_n satisfy Γf_n(x)-qf_n(x)=0. If f_n(x), the first and second ordinary derivatives at x, and the complete compensated negative-jump integrals converge respectively to the corresponding quantities for f, then Γf(x)-qf(x)=0. The explicit four separate convergence assumptions specify precisely what a genuine finite-exponential approximation or stopped Dynkin argument must establish; this theorem makes no unsupported claim that those convergences hold for a q-scale function.
-- source:
--   Exact Lévy generator definition 933ced80, continuity of real addition/multiplication and uniqueness of limits; finite exponential q-generator harmonic family 5d993efc gives a source of approximants if domain convergence can be proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_generator_q_harmonic_of_pointwise_jet_and_jump_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (f : ℝ → ℝ) (fn : ℕ → ℝ → ℝ)
    (hint : X.GeneratorIntegrable f x)
    (hval : Tendsto (fun n : ℕ => fn n x) atTop (nhds (f x)))
    (hfirst : Tendsto (fun n : ℕ => deriv (fn n) x)
      atTop (nhds (deriv f x)))
    (hsecond : Tendsto (fun n : ℕ => iteratedDeriv 2 (fn n) x)
      atTop (nhds (iteratedDeriv 2 f x)))
    (hjump : Tendsto
      (fun n : ℕ => ∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (fn n) x y ∂X.ν)
      atTop
      (nhds (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand f x y ∂X.ν)))
    (hharm : ∀ n : ℕ,
      X.generator (fn n) x - q * fn n x = 0) :
    X.GeneratorIntegrable f x ∧
      X.generator f x - q * f x = 0 := by sorry
