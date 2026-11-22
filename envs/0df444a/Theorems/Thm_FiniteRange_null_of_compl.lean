-- Prove2me | Theorems.Thm_FiniteRange_null_of_compl
-- name    : FiniteRange.null_of_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:24:51.777148+00:00
-- url     : https://prove2.me/theorems/06adc868-1b5a-4822-9d8f-ac4c3baa3db7
-- title:
--   Finite Range: null of compl
-- statement:
--   The Finite Range construction uses the null of compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L167-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L167-L174

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory

theorem FiniteRange.null_of_compl {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) (hX : AEMeasurable X μ)
    [FiniteRange X] :
    (μ.map X) (FiniteRange.toFinset X : Set G)ᶜ = 0 := by sorry
