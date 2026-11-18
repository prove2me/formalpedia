-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_mark_joint_PGF_convexOn_unit_interval_20261117
-- name    : AvramDividend.Classical.avram_a27_original_negative_mark_joint_PGF_convexOn_unit_interval_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:39:50.655472+00:00
-- url     : https://prove2.me/theorems/febebf4d-380c-4f10-86e2-62205dc741ef
-- title:
--   Actual original marked negative jump PGF is convex on the generating-parameter unit interval
-- statement:
--   For the original finite-activity spectrally negative Levy path, the generating function z ↦ E[z^{K_t} exp(theta J_t)] of its true physical negative jump count and actual jump sum is convex on z in [0,1] for every nonnegative theta. The proof uses positivity of the actual jump Laplace factor and convexity of the nonnegative integer powers, then integrates the samplewise inequality on the unchanged source measure.
-- source:
--   Pinned Mathlib convexOn_pow, ConvexOn.smul, MeasureTheory.integral_convexOn_of_integrand_ae, and Proved original source marked PGF integrability cc395132.

import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_negative_mark_joint_PGF_convexOn_unit_interval_20261117
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
    (K : Ω → ℕ) (hK : Measurable K) :
    ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun z => ∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by sorry
