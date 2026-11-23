-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_positive_original_marked_poisson_moment_from_A92
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_positive_original_marked_poisson_moment_from_A92
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:23:16.081903+00:00
-- url     : https://prove2.me/theorems/056f0e49-d14a-4c92-a011-d34e977400ed
-- title:
--   Positive-horizon original negative-jump Poisson marked moments from A92
-- statement:
--   The physical same-space A92 marked-Poisson enumeration implies the positive-time and positive-Laplace original negative-jump exponential moment witness. Use proved original exponential integrability, independent marked random-sum Laplace identity, and the general Poisson probability generating function. The physical A92 source construction remains Open.
-- source:
--   Original A77 physical Poisson model 9262691d, existing A92 original finite-jump enumeration ed91ec27, proved A85 integrability, chat06 random-sum theorem, and chat06 Poisson PGF.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_positive_original_marked_poisson_moment_from_A92
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hNu : X.ν ≠ 0) (ht : 0 < t) (hθpos : 0 < θ) :
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) := by sorry
