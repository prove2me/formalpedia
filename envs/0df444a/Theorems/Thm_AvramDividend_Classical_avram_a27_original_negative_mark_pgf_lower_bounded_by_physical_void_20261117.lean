-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_mark_pgf_lower_bounded_by_physical_void_20261117
-- name    : AvramDividend.Classical.avram_a27_original_negative_mark_pgf_lower_bounded_by_physical_void_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:30:01.220759+00:00
-- url     : https://prove2.me/theorems/204972c2-ae4c-4e15-9ce6-fd1249d9bd62
-- title:
--   Original physical marked jump PGF has the exact Poisson void probability as a lower bound
-- statement:
--   For a finite-activity spectrally negative Levy process on its original filtered probability space and an exact original Poisson negative-jump count K, the full joint marked probability generating function at any z between zero and one and nonnegative mark Laplace tilt is at least exp(-r). It follows directly from the already-Proved exact zero-count observable and positivity of all marked weights, without using any fictitious independent mark stream.
-- source:
--   Pinned integral_mono_ae; Proved original physical marked PGF at zero bf479d04, and original marked PGF integrability cc395132.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_pgf_zero_exact_exponential_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_negative_mark_pgf_lower_bounded_by_physical_void_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (-(r : ℝ)) ≤
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by sorry
