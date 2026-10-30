-- Prove2me | Theorems.Thm_ChenCheckout_Protection_proposition_5
-- name    : ChenCheckout.Protection.proposition_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T06:47:50.600028+00:00
-- url     : https://prove2.me/theorems/dc1ac709-530b-4994-bd1e-090f0f607375
-- title:
--   Proposition 5 — Truncated-expectation bound
-- statement:
--   On any probability space, let X be a measurable real random variable with 0≤X≤b almost surely, where b≥0, and E[X]≥b/2. For any real a with 0≤a≤b,
--
--   $$\mathbb E[\min\{X,a\}]\ge a/2.$$
--
--   The domain includes b=0, arbitrary real distributions and arbitrary underlying probability spaces. Boundedness implies integrability.
--
--   Differences from the source:
--   - encoding: a random variable distributed over [0,b] → a measurable real function on an arbitrary probability space with almost-sure interval bounds; reason: the usual probabilistic convention; boundedness supplies integrability without an extra restriction
-- source:
--   Chen, Ma, Simchi-Levi and Xin (2024), Mathematics of Operations Research 49(1), 297–325, https://doi.org/10.1287/moor.2023.1357, Proposition 5, printed p. 315 / PDF 19

import Mathlib

open MeasureTheory

namespace ChenCheckout.Protection

theorem proposition_5 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 b)
    (hmean : b/2 ≤ ∫ ω, X ω ∂μ) (a : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a/2 ≤ ∫ ω, min (X ω) a ∂μ := by sorry

end ChenCheckout.Protection
