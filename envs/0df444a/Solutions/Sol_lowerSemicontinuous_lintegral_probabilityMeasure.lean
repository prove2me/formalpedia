-- Prove2me | solution 1 for lowerSemicontinuous_lintegral_probabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:51.690403+00:00
-- url     : https://prove2.me/submissions/dfaa8342-291f-4abf-82d6-aba13517fdbf

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
import Theorems.Thm_LowerSemicontinuous_lintegral_le_liminf

set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal
theorem _root_.solution
    {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [PolishSpace W] [BorelSpace W]
    {f : W → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun γ : ProbabilityMeasure W => ∫⁻ x, f x ∂(γ : Measure W) := by
  intro γ y hy
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- extract a sequence `γs → γ` along which the integrals stay `≤ y`;
  -- `ProbabilityMeasure W` is metrizable, hence `𝓝 γ` is countably generated
  have h_freq : ∃ᶠ ν : ProbabilityMeasure W in 𝓝 γ, ∫⁻ x, f x ∂(ν : Measure W) ≤ y :=
    hcon.mono fun ν hν => not_lt.mp hν
  obtain ⟨γs, hγs_tendsto, hγs_le⟩ := exists_seq_forall_of_frequently h_freq
  -- portmanteau: the open-set liminf condition holds along `γs`
  have h_opens : ∀ G, IsOpen G →
      (γ : Measure W) G ≤ atTop.liminf fun i => (γs i : Measure W) G := fun _ hG =>
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hγs_tendsto hG
  have h_le : ∫⁻ x, f x ∂(γ : Measure W) ≤
      atTop.liminf fun i => ∫⁻ x, f x ∂(γs i : Measure W) :=
    hf.lintegral_le_liminf h_opens
  have h_lim_le : (atTop.liminf fun i => ∫⁻ x, f x ∂(γs i : Measure W)) ≤ y :=
    liminf_le_of_frequently_le' (Frequently.of_forall hγs_le)
  exact absurd (hy.trans_le (h_le.trans h_lim_le)) (lt_irrefl y)
