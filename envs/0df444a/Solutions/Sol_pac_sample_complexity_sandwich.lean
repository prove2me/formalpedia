-- Prove2me | solution 1 for pac_sample_complexity_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:27.618336+00:00
-- url     : https://prove2.me/submissions/6b53b5ac-9621-42f4-986c-1be169f8dfc9

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PAC
public import Theorems.Thm_sample_complexity_upper_of_pac_witness
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas
public import Theorems.Thm_sample_complexity_lower_bound


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    [MeasurableConceptClass X C] :
    PACLearnable X C →
      ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
            ∀ c ∈ C,
              MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
                { xs : Fin (mf ε δ) → X |
                  D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                    ≤ ENNReal.ofReal ε }
                ≥ ENNReal.ofReal (1 - δ)) ∧
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          SampleComplexity X C ε δ ≤ mf ε δ) ∧
        (∀ (d : ℕ), VCDim X C = d →
          ∀ (ε δ : ℝ), 0 < ε → ε ≤ 1 / 4 →
            0 < δ → δ ≤ 1 → δ ≤ 1 / 7 → 1 ≤ d →
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ ∧
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε δ) := by
  have hmeas_C := MeasurableConceptClass.hmeas_C C
  have hc_meas := MeasurableConceptClass.hc_meas C
  have hWB := MeasurableConceptClass.hWB C
  intro hPAC
  rcases hPAC with ⟨L, mf, hmf⟩
  refine ⟨L, mf, hmf, ?_, ?_⟩
  · intro ε δ hε hδ
    exact sample_complexity_upper_of_pac_witness X C L mf hmf ε δ hε hδ
  · intro d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos
    have hlower :=
      sample_complexity_lower_bound X C d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos hmeas_C hc_meas hWB
    have hupper :=
      sample_complexity_upper_of_pac_witness X C L mf hmf ε δ hε hδ
    exact ⟨hlower, le_trans hlower hupper⟩
