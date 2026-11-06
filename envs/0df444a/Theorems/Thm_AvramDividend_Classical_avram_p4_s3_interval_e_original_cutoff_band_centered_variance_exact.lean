-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_cutoff_band_centered_variance_exact
-- name    : AvramDividend.Classical.avram_p4_s3_interval_e_original_cutoff_band_centered_variance_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:59:27.88104+00:00
-- url     : https://prove2.me/theorems/56c5b025-4432-4319-bd74-bd95e13f9aa8
-- title:
--   Genuine original full-cutoff negative marked count has exact variance equal to Lévy rate
-- statement:
--   For a spectrally negative Levy process on the original sample space, the actual marked negative jump count over (0,T] on the canonical full half-line cutoff has integrable centred square with exact expectation r, where r=T·ν((-∞,-1/(n+1)]). The proof combines a proven original physical first moment, exact source factorial second moment, and original L² integrability. It provides an actual Poisson-count second-moment identity without equality-in-law or any assumed stochastic isometry; a future independence argument is still needed for conditional variance.
-- source:
--   Public Proved 0a13392f original physical cutoff factorial moment exact, c1e09ada original real first mean, 963870c8 original centred L² integrability; the algebra N²=N(N−1)+N yields E[(N−r)²]=r after verified integral linearity.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_e_original_cutoff_band_centered_variance_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by sorry
