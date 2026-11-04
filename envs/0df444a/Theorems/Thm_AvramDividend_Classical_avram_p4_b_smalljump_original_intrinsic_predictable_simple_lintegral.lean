-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_predictable_simple_lintegral
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_predictable_simple_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:44:29.60283+00:00
-- url     : https://prove2.me/theorems/8c88988c-3875-4fbf-9f34-945e1df8d005
-- title:
--   Original intrinsic Lévy jump count: finite predictable-simple nonnegative compensation
-- statement:
--   For the genuine original source intrinsic marked count, if each predictable rectangle has its P2 conditional intensity identity and each sample-path count functional is measurable, then a finite sum of their event-indicated count functionals has expected value equal to the corresponding sum of deterministic compensator intensities. The exact original counting object is present in hJsource. This result handles finite simple integrands only and does not claim a stochastic-integral L² extension.
-- source:
--   Original intrinsic count from P2 canonical 393b03a8; Mathlib lintegral_finsetSum and lintegral_indicator. The unresolved P2 cell law remains hCell, and counting measurability remains hJmeas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_predictable_simple_lintegral
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (S : Finset ι)
    (s t : ι → ℝ≥0) (A : ι → Set Ω)
    (B : ι → Set ℝ) (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ∈ S, ∀ ω,
      J i ω = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i))
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (hCell : ∀ i ∈ S,
      (∫⁻ ω in A i, J i ω ∂P) =
        P (A i) * ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) :
    (∫⁻ ω, ∑ i ∈ S, (A i).indicator (J i) ω ∂P) =
      ∑ i ∈ S, P (A i) * ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i) := by sorry
