-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja30_original_marked_strip_future_borel_count_covariance_zero
-- name    : AvramDividend.Classical.avram_ja30_original_marked_strip_future_borel_count_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:48:33.991196+00:00
-- url     : https://prove2.me/theorems/3bc637bc-37cb-4eda-aa1f-e576b6dee99f
-- title:
--   Original past signed marked-strip and future Borel count have zero covariance
-- statement:
--   The genuinely original past compensated real-mark strip is L2 adapted and orthogonal to the subsequent centred physical count on any separated negative Borel cell. This follows from proven original-space L2 and predictable compensated count properties, with no auxiliary Brownian or Poisson space.
-- source:
--   Original marked-strip martingale covariance input for JA28 physical Borel mark approximation and original Gaussian noise source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja30_original_marked_strip_future_borel_count_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m)
    (s t : ℝ≥0) (hst : s ≤ t)
    (cut : ℕ) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
    let S : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : Ω → ℝ := fun ω =>
      (∫ p in (Ioc 0 s ×ˢ S), p.2 ∂NX ω) -
        (s : ℝ) * (∫ z in S, z ∂X.ν)
    let N : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
    (∫ ω, H ω * ((N ω).toReal - r) ∂P) = 0 := by sorry
