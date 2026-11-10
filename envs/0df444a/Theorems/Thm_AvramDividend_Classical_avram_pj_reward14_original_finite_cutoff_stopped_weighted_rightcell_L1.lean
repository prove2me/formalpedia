-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward14_original_finite_cutoff_stopped_weighted_rightcell_L1
-- name    : AvramDividend.Classical.avram_pj_reward14_original_finite_cutoff_stopped_weighted_rightcell_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:32:11.040331+00:00
-- url     : https://prove2.me/theorems/342fb2d1-9e23-4613-a801-5b52badbbf51
-- title:
--   Original stopped finite-cutoff weighted right-cell L1 vanishing from physical jump count
-- statement:
--   For the original spectrally negative Levy path, every bounded physical stopping clock and approaching measurable grid right endpoint, and any integrable discounted finite-cutoff nonlinear Taylor error dominated by a constant times the original stopped negative-jump count, the expected absolute error vanishes. This transfers the proved final stop-straddling cell count to source weighted calculus without treating the floor of a stopping time as a stopping time.
-- source:
--   Derived by integral monotonicity, scalar multiplication, and the original physical count L1 theorem a39752ef-d1f2-40cd-aff9-d415a7b54277. Necessary fixed-cutoff weighted remainder transfer in root-connected 0b1a879a stopped Ito Meyer proof; further full terminal plus cash source identification is still required.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward14_original_finite_cutoff_stopped_weighted_rightcell_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (hτ : Measurable τ) (he : ∀ k, Measurable (e k))
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω))) :
    let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : ℕ → Ω → ℝ := fun k ω =>
      ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal
    ∀ (F : ℕ → Ω → ℝ) (K : ℝ),
      0 ≤ K →
      (∀ k, Integrable (F k) P) →
      (∀ k, Integrable (N k) P) →
      (∀ k ω, |F k ω| ≤ K * N k ω) →
      Tendsto (fun k => ∫ ω, |F k ω| ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
