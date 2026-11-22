-- Prove2me | solution 1 for sauer_shelah_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:38.75861+00:00
-- url     : https://prove2.me/submissions/187d8d32-c748-4f5e-8096-146a0f8ef3ec

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
public import Theorems.Thm_growth_function_le_sauer_shelah


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (d : ℕ)
    (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) (m : ℕ) (hm : d ≤ m) :
    GrowthFunction X (↑C : Set (X → Bool)) m ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose m i :=
  -- M-Bridge: factored through Bridge.lean infrastructure
  growth_function_le_sauer_shelah C d hd m hm
