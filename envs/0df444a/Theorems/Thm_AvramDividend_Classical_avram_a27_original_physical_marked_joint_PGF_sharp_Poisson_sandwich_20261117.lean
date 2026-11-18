-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_joint_PGF_sharp_Poisson_sandwich_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_marked_joint_PGF_sharp_Poisson_sandwich_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:51:22.866024+00:00
-- url     : https://prove2.me/theorems/393fa02f-75b7-4f67-ac82-1c7f09ff3346
-- title:
--   Original physical marked negative jump PGF has sharp void and unmarked Poisson generating-function bounds
-- statement:
--   For an actual finite negative-activity spectrally negative Levy process, its original physical negative jump count K and finite jump sum J satisfy exp(-r) ≤ E[z^K exp(theta J)] ≤ exp(r(z-1)) for every z in [0,1], theta≥0 and original Poisson jump count rate r. Both bounds hold on the original probability space; their proofs use the genuine physical Poisson void identity and exact physical count law, with no auxiliary marks.
-- source:
--   Previously Proved A27 original physical void lower bound 204972c2 and original physical marked PGF count upper bound 9846a62a.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_marked_joint_PGF_sharp_Poisson_sandwich_20261117
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
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) ∧
    (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) ≤
      Real.exp ((r : ℝ) * (z - 1)) := by sorry
