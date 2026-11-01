-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pointwise_indicator_span_l2_lift
-- name    : AvramDividend.Classical.avram_wave4_p1_pointwise_indicator_span_l2_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:28:57.409268+00:00
-- url     : https://prove2.me/theorems/af412b58-2bd6-4464-8dc0-ff290f2da7bc
-- title:
--   Finite pointwise indicator expansions lift without loss to the actual L² simple span
-- statement:
--   Let G be any family of measurable finite-measure sets on an original measurable space, and let s be measurable with finite measure. Suppose the pointwise indicator of s is a finite real linear combination of pointwise generator indicators. Prove the actual Lp ℝ 2 μ indicatorConstLp of s belongs to the FINITE real submodule span of the generator indicatorConstLp elements, with all measurability and finite-measure proofs correctly transported. The hypothesis is only the already independently provable algebraic pointwise span, not the desired L² span. Prove using Submodule.span_induction with MemLp indicator, addition and real scalar multiplication closure, and pinned MemLp.toLp_add, toLp_const_smul, toLp_zero. This fixes the precise pointwise-to-L² gap between Pi Boolean approximation and dense elementary stochastic integration.
-- source:
--   Pinned Mathlib MeasureTheory.Function.LpSpace.Indicator indicatorConstLp and memLp_indicator_const; Function.LpSpace.Basic MemLp.toLp_add, MemLp.toLp_const_smul, MemLp.toLp_zero. Applies to P1 Proved Boolean finite real span UUID 2a12efad and forthcoming Pi-system corollary c58acfdd.

import Mathlib
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_pointwise_indicator_span_l2_lift
    {α : Type*} [mα : MeasurableSpace α]
    (μ : Measure α) (G : Set (Set α))
    (hGm : ∀ t : Set α, t ∈ G → MeasurableSet t)
    (hGfinite : ∀ t : Set α, t ∈ G → μ t ≠ ⊤)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (hSpan :
      let χ : Set α → (α → ℝ) :=
        fun t => Set.indicator t (fun _ => (1 : ℝ))
      χ s ∈ Submodule.span ℝ
        {v : α → ℝ | ∃ (t : Set α), t ∈ G ∧ χ t = v}) :
    indicatorConstLp (2 : ℝ≥0∞) hs hμs (1 : ℝ) ∈
      Submodule.span ℝ
        {v : Lp ℝ (2 : ℝ≥0∞) μ |
          ∃ (t : Set α) (ht : t ∈ G)
            (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
            indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v} := by sorry
