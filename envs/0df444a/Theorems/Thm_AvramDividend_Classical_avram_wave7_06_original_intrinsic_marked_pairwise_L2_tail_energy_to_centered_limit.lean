-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_pairwise_L2_tail_energy_to_centered_limit
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_pairwise_L2_tail_energy_to_centered_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:12:07.712907+00:00
-- url     : https://prove2.me/theorems/20281d57-c24d-4220-9d6d-bad25b98911d
-- title:
--   Original intrinsic marked compensator pairwise L2 tail-energy bound yields centred L2 limit
-- statement:
--   For literal intrinsic source-jump minus predictable compensator truncations represented in real L2(P), a pairwise variance/isometry estimate by a vanishing earlier-band energy E(m) suffices for Cauchy convergence and zero expectation. The quantitative tail hypothesis is the exact new remaining marked small-jump estimate and may follow from source marked-cell L2 isometry and the Taylor quadratic Lévy tail.
-- source:
--   W7-06 original marked-cell tail variance criterion for actual X-jump measure, under explicit L2 representation and energy hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_pairwise_L2_tail_energy_to_centered_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (clock : Measure ℝ≥0)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (B : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hRep : ∀ n, (M n : Ω → ℝ) =ᵐ[P] fun ω =>
      (∫ p, (B n).indicator G ((p.1, ω), p.2) ∂(NX ω)) -
        ∫ t, ∫ z, (B n).indicator G ((t, ω), z) ∂X.ν ∂clock)
    (E : ℕ → ℝ)
    (hEnergySmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m, N ≤ m → E m < ε ^ 2)
    (hPairwise : ∀ m n, m ≤ n →
      (dist (M m) (M n)) ^ 2 ≤ E m)
    (hCentered : ∀ k, (∫ ω, M k ω ∂P) = 0) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
