-- Prove2me | Theorems.Thm_FiniteRange_real_full
-- name    : FiniteRange.real_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:29:10.171973+00:00
-- url     : https://prove2.me/theorems/65795d99-4596-4de3-be7a-e931eae5bfc0
-- title:
--   Finite Range: real full
-- statement:
--   The Finite Range construction uses the real full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L159-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L159-L163

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory

theorem FiniteRange.real_full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω
      → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X).real (FiniteRange.toFinset X) = μ.real Set.univ := by sorry
