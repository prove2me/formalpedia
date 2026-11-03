-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_stopped_physical_discounted_drift_L1
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_stopped_physical_discounted_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:30:53.943545+00:00
-- url     : https://prove2.me/theorems/da1766f8-d986-41b8-8c1a-d9d6e3e24f94
-- title:
--   Original BV pre-ruin discounted physical drift is L1 on the actual finite source product clock
-- statement:
--   For the original Lévy source with its built-in probability measure and an actual dividend path, the deterministic physical drift coefficient multiplied by the finite-horizon nonincreasing exponential discount is integrable over every measurable strict pre-ruin, positive, sub-cap predictable-left-limit region. No source-jump compensation, HJB sign, smoothness or positive drift assumption is needed. This removes the left IntegrableOn premise from the Proved W7-17 expected discounted drift-generator cover.
-- source:
--   Original BV complement helper b4a4ea2a-7049-4321-8910-90e7a3971c07, left IntegrableOn premise. Uses SpectrallyNegativeLevy.isProbability, finite Lebesgue interval, physical real-to-nonnegative time map and bounded q≥0 exponential discount. Compatible with W7-04 hEnvelope and T=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_stopped_physical_discounted_drift_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (C : ℝ≥0∞)
    (hS : MeasurableSet
      {p : ℝ≥0 × Ω |
        p.1 ≤ T ∧
        (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C}) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C}
    IntegrableOn
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))) * X.drift) S μ := by sorry
