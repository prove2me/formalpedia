-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a377m_masked_gaussian_C2_compensator_measurable
-- name    : AvramDividend.Classical.avram_ga_a377m_masked_gaussian_C2_compensator_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:57:33.244209+00:00
-- url     : https://prove2.me/theorems/34b53d9b-4b29-4bc9-9ae0-ac0d6be4fba5
-- title:
--   Measurability of the masked finite Gaussian C2 jet compensation sum
-- statement:
--   A finite sum of Gaussian centred linear and quadratic compensation terms evaluated at measurable positive reserve values is strongly measurable almost everywhere when the first and second derivative fields are continuous on the positive half-line, even if the unmasked reserve values may leave the positive domain.
-- source:
--   The Gaussian stopped-physical-mesh compensator in the source-faithful a146 original Levy dividend spatial residual. The masked derivative extension argument is independent of the original process and retains the full source mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a377m_masked_gaussian_C2_compensator_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (w : ℝ → ℝ)
    (hw1 : ContinuousOn (deriv w) (Ioi (0 : ℝ)))
    (hw2 : ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)))
    (m : ℕ) (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω | A i ω})
    (Y R : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hR : ∀ i, Measurable (R i))
    (hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m, A i ω → 0 < Y i ω)
    (d c σ : ℝ) (E : ℕ → ℝ) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, if A i ω then
        E i * (deriv w (Y i ω) * (R i ω - d * c) +
          iteratedDeriv 2 w (Y i ω) / 2 *
            ((R i ω - d * c)^2 - d * σ^2)) +
          d * E i * (σ^2 / 2 * iteratedDeriv 2 w (Y i ω) +
            c * deriv w (Y i ω))
      else 0) P := by sorry
