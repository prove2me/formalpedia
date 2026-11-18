-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_pgf_zero_exact_exponential_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_marked_pgf_zero_exact_exponential_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:11:19.519315+00:00
-- url     : https://prove2.me/theorems/bf479d04-08fd-4df3-bdfa-3097ff0fc840
-- title:
--   Original physical marked-jump PGF at zero equals the exact Poisson void exponential
-- statement:
--   For the actual original spectrally negative finite-activity Lévy physical negative-jump sum J and count K, the marked PGF at zero equals exp(-r), where r is the exact Poisson count rate. This is the exact zero-argument boundary condition for the original marked Poisson Campbell/Laplace functional, not a surrogate process.
-- source:
--   Server-Proved original physical marked joint PGF at z=0 and Mathlib poissonMeasure_real_singleton.

import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_marked_pgf_zero_exact_exponential_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
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
      Real.exp (-(r : ℝ)) := by sorry
