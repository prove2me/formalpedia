-- Prove2me | Theorems.Thm_FiniteRange_ae_mem_toFinset
-- name    : FiniteRange.ae_mem_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:29:13.024885+00:00
-- url     : https://prove2.me/theorems/b5f734cf-0086-454a-be75-77d70383d4b2
-- title:
--   Finite Range: ae mem to Finset
-- statement:
--   The Finite Range construction uses the ae mem to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L176-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/Defs.lean#L176-L179

module
public import Mathlib.MeasureTheory.Measure.Map
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory

theorem FiniteRange.ae_mem_toFinset {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) (hX : AEMeasurable X μ)
    [FiniteRange X] :
    ∀ᵐ x ∂(μ.map X), x ∈ (FiniteRange.toFinset X : Set G) := by sorry
