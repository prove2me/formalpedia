-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_joint_pgf_at_zero_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_mark_joint_pgf_at_zero_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:43:07.268355+00:00
-- url     : https://prove2.me/theorems/04ed5cae-a265-48c4-88a3-afa6fb596e0d
-- title:
--   Actual original negative-jump marked Poisson generating-function initial value at z zero
-- statement:
--   For the actual original spectrally negative Lévy path on its unchanged probability space, the generating-function expectation E[0^K exp(theta J)] equals the zero-count Poisson probability. This is the boundary value needed to solve the source marked-Poisson Volterra generating-function equation.
-- source:
--   Proved exact original physical zero count-cell Laplace integral and measurable indicator identity 0^K equals one exactly on K=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- At the zero PGF argument, the original physical marked-count Laplace expectation is the zero-cell Poisson mass. -/

theorem AvramDividend.Classical.avram_a27_original_physical_negative_mark_joint_pgf_at_zero_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    (∫ ω, (0 : ℝ) ^ (K ω) * Real.exp (θ * J ω) ∂P) =
      (poissonMeasure r).real {0} := by sorry
