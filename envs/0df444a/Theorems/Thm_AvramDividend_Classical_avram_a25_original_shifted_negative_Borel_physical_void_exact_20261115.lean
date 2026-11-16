-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
-- name    : AvramDividend.Classical.avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:22:15.58527+00:00
-- url     : https://prove2.me/theorems/103eb83a-2079-4868-ba5a-5f4c1df8574c
-- title:
--   Exact exponential probability of zero original physical negative-Borel jumps in every shifted deterministic time interval
-- statement:
--   For the original finite-negative-intensity spectrally negative Lévy process, the original P-probability of no B-marked negative jumps on any interval (s,s+T] equals exp(−Tν(B)), for arbitrary measurable B contained in the negative halfline. Proved exact origin void probability 786aeafb and original Borel marked-count stationary law 37abf3aa give this by comparing the zero-event preimages under equal pushforward laws, using the proved source marked count measurability. The result and independent counts provide exact one-cell void laws across every deterministic Poisson grid without using any companion stochastic process.
-- source:
--   Proved original physical Borel void at origin 786aeafb; source count stationarity 37abf3aa; count measurable 5cb1e247.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc s (s + T) ×ˢ B) = 0}).toReal =
      Real.exp (-((T : ℝ) * (X.ν B).toReal)) := by sorry
