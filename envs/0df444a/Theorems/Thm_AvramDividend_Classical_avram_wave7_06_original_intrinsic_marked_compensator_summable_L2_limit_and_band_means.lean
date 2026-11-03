-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_compensator_summable_L2_limit_and_band_means
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_compensator_summable_L2_limit_and_band_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:10:19.421307+00:00
-- url     : https://prove2.me/theorems/2808947d-c840-4a1f-9fb6-f179175d17fa
-- title:
--   Exact original marked Lévy truncation mean compensation and summable L2 limit
-- statement:
--   For the literal original X-jump measure, if each band-compensated marked integral has an actual original-space L2 representative, its consecutive L2 distances are summable, and its mean is zero, the physical source jump minus compensator has zero expectation at every band and the L2 limit has mean zero. The exact missing energy and centring hypotheses remain explicit. No auxiliary Poisson space is substituted.
-- source:
--   W7-06 original marked-cell L2/L1 source-integral interface, reducing the limit to validated square-summable source truncations and exact representation hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_compensator_summable_L2_limit_and_band_means
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
    (hSteps : Summable (fun k => dist (M k) (M (k + 1))))
    (hCentered : ∀ k, (∫ ω, M k ω ∂P) = 0) :
    (∀ n, (∫ ω,
      ((∫ p, (B n).indicator G ((p.1, ω), p.2) ∂(NX ω)) -
        ∫ t, ∫ z, (B n).indicator G ((t, ω), z) ∂X.ν ∂clock) ∂P) = 0) ∧
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
