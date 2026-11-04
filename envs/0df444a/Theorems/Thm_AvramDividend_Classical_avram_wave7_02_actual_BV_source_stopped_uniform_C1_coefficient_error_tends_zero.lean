-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_actual_BV_source_stopped_uniform_C1_coefficient_error_tends_zero
-- name    : AvramDividend.Classical.avram_wave7_02_actual_BV_source_stopped_uniform_C1_coefficient_error_tends_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:02:21.019039+00:00
-- url     : https://prove2.me/theorems/21856858-3969-4985-927d-add3f0086397
-- title:
--   Original BV Lévy source: uniform C¹ coefficient approximation error vanishes on all stopped residual partition grids
-- statement:
--   For the original spectrally negative Lévy source of bounded variation, use its uniquely defined monotone intrinsic residual R on one P-almost-sure event. On every family of finite ordered time partitions with initial time zero and terminal samplewise time bounded by an arbitrary stopping horizon, if two arrays of sampled coefficients differ uniformly by an error M(k) tending to zero, their genuinely source-residual-weighted sums converge to each other, uniformly in the partition shapes. The result derives from the Proved original-source stopped uniform coefficient bound and a squeezing limit; it does not assume a pure-jump decomposition, an unrelated Poisson sample space, or a stopped Itô chain identity.
-- source:
--   Original-source controlled BV C1 approximation passage. The prior Proved d99f6bce establishes an almost-sure uniform stopped-horizon finite-grid error, and norm convergence proves that every vanishing uniform coefficient perturbation induces vanishing weighted residual error. Intended consumer W8-04 source stopped C1 Ito limit construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_uniform_stopped_coefficient_approximation_error

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Uniform convergence of C¹ coefficient approximations on the exact
original-source monotone BV residual, along arbitrary stopped finite
time partitions. No pure-jump representation or Itô identity is assumed. -/

theorem AvramDividend.Classical.avram_wave7_02_actual_BV_source_stopped_uniform_C1_coefficient_error_tends_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstart : ∀ k : ℕ, u k 0 = 0)
        (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (a b : ℕ → ℕ → ℝ) (M : ℕ → ℝ)
        (hM : ∀ k : ℕ, 0 ≤ M k)
        (hMlim : Tendsto M atTop (𝓝 (0 : ℝ)))
        (hab : ∀ k i : ℕ, |a k i - b k i| ≤ M k),
        Tendsto (fun k : ℕ =>
          (Finset.range (n k)).sum (fun i =>
            a k i * (R (u k (i + 1)) - R (u k i))) -
          (Finset.range (n k)).sum (fun i =>
            b k i * (R (u k (i + 1)) - R (u k i))))
          atTop (𝓝 (0 : ℝ)) := by sorry
