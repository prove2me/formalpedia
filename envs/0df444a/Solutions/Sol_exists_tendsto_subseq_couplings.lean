-- Prove2me | solution 1 for exists_tendsto_subseq_couplings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:54.31198+00:00
-- url     : https://prove2.me/submissions/99486430-34d2-4a0d-b827-5fd3d30db12b

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Theorems.Thm_isTightMeasureSet_range_of_tendsto
import Theorems.Thm_isTightMeasureSet_couplings_of_isTightMeasureSet
import Theorems.Thm_probabilityMeasure_map_eq_iff


set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    {μs : ℕ → ProbabilityMeasure A} {μ : ProbabilityMeasure A}
    {νs : ℕ → ProbabilityMeasure B} {ν : ProbabilityMeasure B}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    {γs : ℕ → ProbabilityMeasure (A × B)}
    (hfst : ∀ n, (γs n : Measure (A × B)).map Prod.fst = (μs n : Measure A))
    (hsnd : ∀ n, (γs n : Measure (A × B)).map Prod.snd = (νs n : Measure B)) :
    ∃ γ : ProbabilityMeasure (A × B),
      (γ : Measure (A × B)).map Prod.fst = (μ : Measure A) ∧
      (γ : Measure (A × B)).map Prod.snd = (ν : Measure B) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (γs ∘ φ) atTop (𝓝 γ) := by
  -- the couplings are a tight family
  have htight : IsTightMeasureSet
      {((γs n : ProbabilityMeasure (A × B)) : Measure (A × B)) | n : ℕ} := by
    have h12 := isTightMeasureSet_couplings_of_isTightMeasureSet
      (isTightMeasureSet_range_of_tendsto hμ)
      (isTightMeasureSet_range_of_tendsto hν)
    refine h12.subset ?_
    rintro m ⟨n, rfl⟩
    exact ⟨⟨n, (hfst n).symm⟩, ⟨n, (hsnd n).symm⟩⟩
  -- Prokhorov: the closure of the range is compact
  have hcomp : IsCompact (closure (Set.range γs)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have hset : {((γ' : ProbabilityMeasure (A × B)) : Measure (A × B)) |
        γ' ∈ Set.range γs}
        = {((γs n : ProbabilityMeasure (A × B)) : Measure (A × B)) | n : ℕ} := by
      ext m
      constructor
      · rintro ⟨γ', ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨γs n, ⟨n, rfl⟩, rfl⟩
    rwa [hset]
  -- extract a convergent subsequence
  obtain ⟨γ, -, φ, hφmono, hφt⟩ :=
    hcomp.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  -- identify the marginals of the limit by continuity of the pushforward
  have hfst' : (γ : Measure (A × B)).map Prod.fst = (μ : Measure A) := by
    refine (probabilityMeasure_map_eq_iff γ μ measurable_fst).mp ?_
    refine tendsto_nhds_unique ?_ (hμ.comp hφmono.tendsto_atTop)
    have hc := MeasureTheory.ProbabilityMeasure.continuous_map
      (Ω := A × B) (Ω' := A) continuous_fst
    have := (hc.tendsto γ).comp hφt
    refine (tendsto_congr fun k => ?_).mp this
    exact (probabilityMeasure_map_eq_iff _ _ measurable_fst).mpr (hfst (φ k))
  have hsnd' : (γ : Measure (A × B)).map Prod.snd = (ν : Measure B) := by
    refine (probabilityMeasure_map_eq_iff γ ν measurable_snd).mp ?_
    refine tendsto_nhds_unique ?_ (hν.comp hφmono.tendsto_atTop)
    have hc := MeasureTheory.ProbabilityMeasure.continuous_map
      (Ω := A × B) (Ω' := B) continuous_snd
    have := (hc.tendsto γ).comp hφt
    refine (tendsto_congr fun k => ?_).mp this
    exact (probabilityMeasure_map_eq_iff _ _ measurable_snd).mpr (hsnd (φ k))
  exact ⟨γ, hfst', hsnd', φ, hφmono, hφt⟩
