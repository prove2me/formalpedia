-- Prove2me | Theorems.Thm_CorrelatedRounding_competitive_bound__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1
-- name    : CorrelatedRounding.competitive_bound__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-17T05:42:59.599111+00:00
-- url     : https://prove2.me/theorems/a8dffa9a-9d9c-4cf9-a471-fb9ad8fa0048
-- title:
--   The facility-use probability bound for Algorithm 1
-- statement:
--   For every Algorithm 1 draw and every assignment that almost surely minimizes the clocks, each facility is used with probability at most `(1 + ln q) y u k`, including when its rate is zero.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Theorem 1, p.11

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw
open CorrelatedRounding MeasureTheory ProbabilityTheory

theorem CorrelatedRounding.competitive_bound__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1 {q K : ℕ} (hq : 1 ≤ q) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Fin K → Fin q → ℝ) (hu : IsInstance u)
    (E : Fin K → Ω → ℝ) (hE : IsAlg1Draw u μ E) (Z : Ω → Fin q → Fin K)
    (hZ : ∀ᵐ ω ∂μ, IsAlg1Output u (fun k => E k ω) (Z ω)) :
    ∀ k, μ (⋃ i, {ω | Z ω i = k}) ≤ ENNReal.ofReal ((1 + Real.log q) * y u k) := by sorry
