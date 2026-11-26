-- Prove2me | solution 1 for lowerSemicontinuous_lintegral_prodMk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:15.173905+00:00
-- url     : https://prove2.me/submissions/f2fec2ff-54b9-491a-a8ad-3f75fda5691d

import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Theorems.Thm_continuous_probabilityMeasure_map_prodMk
import Theorems.Thm_lowerSemicontinuous_lintegral_probabilityMeasure


set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
variable {H W : Type*}
  [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]
theorem _root_.solution
    {f : H × W → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun p : H × ProbabilityMeasure W =>
      ∫⁻ z, f (p.1, z) ∂(p.2 : Measure W)) := by
  have hkey : (fun p : H × ProbabilityMeasure W =>
        ∫⁻ z, f (p.1, z) ∂(p.2 : Measure W))
      = (fun γ : ProbabilityMeasure (H × W) =>
          ∫⁻ q, f q ∂(γ : Measure (H × W)))
        ∘ (fun p : H × ProbabilityMeasure W =>
            ProbabilityMeasure.map p.2
              (measurable_prodMk_left (x := p.1)).aemeasurable) := by
    funext p
    simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
    rw [lintegral_map hf.measurable measurable_prodMk_left]
  rw [hkey]
  exact (lowerSemicontinuous_lintegral_probabilityMeasure hf).comp
    continuous_probabilityMeasure_map_prodMk
