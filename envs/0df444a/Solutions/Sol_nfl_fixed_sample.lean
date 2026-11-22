-- Prove2me | solution 1 for nfl_fixed_sample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:48.196609+00:00
-- url     : https://prove2.me/submissions/583b7039-f381-4ece-9f35-91de976c7f0b

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
public import Theorems.Thm_nfl_core


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hX : 2 ≤ Fintype.card X) (m : ℕ) (hm : 2 * m ≤ Fintype.card X)
    (L : BatchLearner X Bool) :
    ∃ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ∧
      ∃ (c : X → Bool),
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              > ENNReal.ofReal (1 / 8) }
          > 0 :=
  -- Routes through nfl_core (Generalization.lean) which captures the
  -- uniform measure construction + counting argument.
  -- A5 NOTE: added [MeasurableSingletonClass X] — needed for uniform measure
  -- to work with Measure.count. This ENRICHES the statement (more structure
  -- on X), it doesn't simplify it. The hypothesis is standard for discrete spaces.
  nfl_core X hX m hm L
