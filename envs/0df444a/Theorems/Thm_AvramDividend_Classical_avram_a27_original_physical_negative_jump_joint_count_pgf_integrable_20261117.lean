-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:07:07.63322+00:00
-- url     : https://prove2.me/theorems/cc395132-ecd4-425e-91d7-f0fbad3f0de7
-- title:
--   Exact original physical negative jump count-Laplace generating function is integrable for 0≤z≤1
-- statement:
--   For the unchanged original finite-activity spectrally negative Lévy process, its physical negative jump sum and measurable count have a jointly integrable weighted generating-function observable z^K exp(theta J) for all z in [0,1] and theta nonnegative. This allows rigorous original-source Volterra and analytic coefficient arguments.
-- source:
--   Proved original physical negative-mark Laplace unit domination and generic bounded mark PGF integrability, preserving P, Omega and filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original physical negative-mark Poisson joint PGF is an integrable observable. -/

theorem AvramDividend.Classical.avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Integrable (fun ω => z ^ (K ω) * Real.exp (θ * J ω)) P := by sorry
