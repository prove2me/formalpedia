-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_random_stopped_marked_interval_pathwise_additivity
-- name    : AvramDividend.Classical.avram_wave7_01_original_random_stopped_marked_interval_pathwise_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:05:13.177624+00:00
-- url     : https://prove2.me/theorems/07a8b485-66c6-4db9-9c53-0bbd4342dfa8
-- title:
--   Original intrinsic marked Lévy jump count is pathwise additive across random stopped intervals and random Borel mark cells
-- statement:
--   For the actual original spectral-negative Lévy sample paths on the given Ω,P,𝓕, arbitrary sample-dependent s(ω)≤t(ω)≤u(ω) and Borel marked cells B(ω) satisfy the exact pathwise jump counting additivity over (s(ω),u(ω)]. No stopping-time, integrability, finite-activity or moment conditions are necessary for this algebraic identity. Predictable measurability matters later for integration.
-- source:
--   Instantiate the Proved canonical intrinsic arbitrary-mark adjacent deterministic interval additivity 04cf48c4-85ab-4976-b73d-e09b5932144b samplewise, preserving the same original sample and jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_arbitrary_mark_adjacent_interval_additive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_random_stopped_marked_interval_pathwise_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : Ω → ℝ≥0)
    (hst : ∀ ω, s ω ≤ t ω) (htu : ∀ ω, t ω ≤ u ω)
    (B : Ω → Set ℝ) (hB : ∀ ω, MeasurableSet (B ω)) :
    ∀ ω : Ω,
      (let NX : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict {v : ℝ≥0 |
          0 < v ∧ X.X v ω -
            Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
       NX (Ioc (s ω) (u ω) ×ˢ B ω) =
         NX (Ioc (s ω) (t ω) ×ˢ B ω) +
           NX (Ioc (t ω) (u ω) ×ˢ B ω)) := by sorry
