-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_existential_both
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_centered_nnreal_compact_existential_both
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:32:16.775037+00:00
-- url     : https://prove2.me/theorems/1ee99950-302f-4186-a786-60f1ac53fc40
-- title:
--   Existential centered original NNReal compact-test grid limit implies a measurable integrable L1 and expected limit
-- statement:
--   On the actual source spectrally negative Levy process with positive NNReal horizon, continuous compact strictly negative test and a.e. existence of a centered NNReal grid limit, choose one real-valued limit without postulating its measurability. The accepted centered NNReal Vitali theorem proves that it is integrable and that the original uncentered grid converges to it strongly in L1 and in genuine Bochner expectations. This aligns with the output form of the P2-H deterministic càdlàg per-sample theorem; P2-H's result is not imported or assumed proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Native almost-everywhere existence of a centered NNReal grid limit yields a single integrable real limit. -/

theorem AvramDividend.Classical.avram_p2_j_ui_original_centered_nnreal_compact_existential_both
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (hex : ∀ᵐ ω ∂P, ∃ z : ℝ, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω) -
           (X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω)))
      atTop (nhds z)) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by sorry
