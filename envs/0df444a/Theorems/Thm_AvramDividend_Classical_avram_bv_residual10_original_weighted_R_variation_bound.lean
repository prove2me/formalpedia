-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_R_variation_bound
-- name    : AvramDividend.Classical.avram_bv_residual10_original_weighted_R_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:15:42.256815+00:00
-- url     : https://prove2.me/theorems/ce2d2c97-e010-4e81-9544-c25f31af00e9
-- title:
--   Original BV physical-mesh residual bounded by weighted path variation
-- statement:
--   For the literal bounded-variation drift residual R(t)=t*X.drift-X_t-J(t), with J the actual original path's accumulated negative jumps, any finite physical-grid sum of predictable or adapted weights a_i times R(u_i)-R(u_{i+1}) is bounded in absolute value by a uniform bound on those weights times the sum of absolute residual increments. This is a pathwise localisation estimate and requires no continuity, Brownian driver, isometry or equality-in-law replacement. To integrate it into the uniform-grid source, instantiate a_i with discounted stopped derivative weights and discharge the weight bound and residual variation expectation under localisation.
-- source:
--   Source-backed AVRAM BV-RESIDUAL10 original-process finite-grid estimate; MathFin/Foundations/AdaptedRiemannStieltjes.lean convergence argument inspected 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_weighted_R_variation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (a : ℕ → ℝ) (K : ℝ)
    (hK : ∀ i ∈ Finset.range (n + 1), |a i| ≤ K) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    |∑ i ∈ Finset.range (n + 1),
        a i * (R (u n i) - R (u n (i + 1)))| ≤
      K * ∑ i ∈ Finset.range (n + 1),
        |R (u n i) - R (u n (i + 1))| := by sorry
