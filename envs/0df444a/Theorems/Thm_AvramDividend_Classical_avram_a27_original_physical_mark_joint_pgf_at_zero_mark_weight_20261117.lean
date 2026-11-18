-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_mark_joint_pgf_at_zero_mark_weight_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_mark_joint_pgf_at_zero_mark_weight_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T22:01:26.938853+00:00
-- url     : https://prove2.me/theorems/857aade2-1115-44b1-986f-3ba43ec2c8cf
-- title:
--   Exact source marked-jump joint PGF at zero mark weight matches the original Poisson count exponential
-- statement:
--   For the actual unchanged physical negative jump sum J and negative-jump Poisson count K on a spectrally negative Levy probability space, the joint count-and-mark PGF at Laplace mark weight theta=0 equals exp(r(z-1)) for any real z. All original jump definitions and source count hypotheses are preserved.
-- source:
--   Already-Proved original-space Poisson count PGF HasLaw transport 009ff568 and the deterministic identity exp(0*J)=1.

import Mathlib.Probability.HasLaw
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_mark_joint_pgf_at_zero_mark_weight_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (J : Ω → ℝ)
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
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z : ℝ) :
    (∫ ω, z ^ (K ω) * Real.exp ((0 : ℝ) * J ω) ∂P) =
      Real.exp ((r : ℝ) * (z - 1)) := by sorry
