-- Prove2me | solution 1 for sample_complexity_upper_of_pac_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:35.658667+00:00
-- url     : https://prove2.me/submissions/b69c1e3d-db91-4e3e-91fc-b5a8eb7c7d39

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

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ)
    (hPAC :
      ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C,
            MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
              { xs : Fin (mf ε δ) → X |
                D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                  ≤ ENNReal.ofReal ε }
              ≥ ENNReal.ofReal (1 - δ)) :
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      SampleComplexity X C ε δ ≤ mf ε δ := by
  intro ε δ hε hδ
  unfold SampleComplexity
  apply Nat.sInf_le
  exact ⟨L, fun D hD c hcC => hPAC ε δ hε hδ D hD c hcC⟩
