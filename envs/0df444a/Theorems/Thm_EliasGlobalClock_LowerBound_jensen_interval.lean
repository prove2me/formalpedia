-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_jensen_interval
-- name    : EliasGlobalClock.LowerBound.jensen_interval
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:23.555178+00:00
-- url     : https://prove2.me/theorems/e343e0c4-6be4-4205-9e02-5c8b086a3e9b
-- title:
--   Fact D.1 — Jensen on arbitrary intervals, convex and concave
-- statement:
--   Let $X$ be an integrable real random variable on a probability space, taking values in a real interval $I$ almost surely, and suppose its mean $m=\mathbb E[X]$ belongs to $I$. Let $\phi:I\to\mathbb R$ have integrable composition $\phi(X)$. Both Jensen assertions hold:
--
--   $$\phi\text{ convex}\ \Longrightarrow\ \phi(m)\le\mathbb E[\phi(X)],\qquad
--   \phi\text{ concave}\ \Longrightarrow\ \mathbb E[\phi(X)]\le\phi(m).$$
--
--   The interval may be open, closed, half-open, unbounded or a singleton. No continuity or boundedness hypothesis is imposed. This fact supplies the expectation and finite-law convexity bounds used by the source's failure estimate.
--
--   Differences from the source:
--   - encoding: a real interval I and a function φ:I→ℝ → a set I with ConvexOn or ConcaveOn and a total real extension of φ; reason: in one dimension the convex-domain clause is exactly the interval condition; the extension outside I has no effect on the almost-surely I-valued variable
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed p.36, PDF p.37, Fact D.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Mathlib

open MeasureTheory

namespace EliasGlobalClock.LowerBound

/-- Fact D.1, printed p.36 / PDF p.37. No continuity or closedness assumption.
ConvexOn/ConcaveOn include convexity of I, hence precisely the interval condition
in one real dimension. The extension of φ outside I is immaterial almost surely. -/
theorem jensen_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set ℝ) (X : Ω → ℝ) (φ : ℝ → ℝ)
    (hX : Integrable X μ) (hXI : ∀ᵐ ω ∂μ, X ω ∈ I)
    (hm : (∫ ω, X ω ∂μ) ∈ I) (hφX : Integrable (fun ω => φ (X ω)) μ) :
    (ConvexOn ℝ I φ → φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ) ∧
    (ConcaveOn ℝ I φ → (∫ ω, φ (X ω) ∂μ) ≤ φ (∫ ω, X ω ∂μ)) := by sorry

end EliasGlobalClock.LowerBound
