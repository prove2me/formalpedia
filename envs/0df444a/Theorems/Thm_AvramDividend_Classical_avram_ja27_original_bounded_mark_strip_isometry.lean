-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja27_original_bounded_mark_strip_isometry
-- name    : AvramDividend.Classical.avram_ja27_original_bounded_mark_strip_isometry
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T21:51:28.125811+00:00
-- url     : https://prove2.me/theorems/2a4be8dd-e5a3-4015-b9fd-633953ab8adc
-- title:
--   Same-space compensated Poisson L2 isometry for bounded measurable mark weights on a finite negative strip
-- statement:
--   For the actual original spectrally negative Levy sample paths, any measurable bounded mark weight on a finite negative activity strip satisfies the exact compensated weighted marked-count variance formula. This directly handles the real mark by choosing g(z)=z and must be proved using the original arbitrary Borel marked-count moments, a finite simple partition approximation, and an L2 limit.
-- source:
--   Core physical finite mark approximation for ec5fe7b6 and 924b87ab; existing Proved finite-activity L2 integrability 85768b34, count variance 6e234a3f, ordered annulus simple isometry 63088608. Requires genuine within-annulus Borel partitions, not only coarse harmonic counts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja27_original_bounded_mark_strip_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (g : ℝ → ℝ),
      Measurable g →
      (∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), |g z| ≤ 1) →
      ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, g z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P →
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν) := by sorry
