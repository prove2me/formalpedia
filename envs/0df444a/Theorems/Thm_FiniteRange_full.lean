-- Prove2me | Theorems.Thm_FiniteRange_full
-- name    : FiniteRange.full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:17.731538+00:00
-- url     : https://prove2.me/theorems/ea9afcd0-ae2c-482c-8c49-3f5f7d98d023
-- title:
--   Finite Range: full
-- statement:
--   The Finite Range construction uses the full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L150-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L150-L157

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory

theorem FiniteRange.full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω
      → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X) (FiniteRange.toFinset X) = μ Set.univ := by sorry
