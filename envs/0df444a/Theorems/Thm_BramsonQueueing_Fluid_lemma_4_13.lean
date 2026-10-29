-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_lemma_4_13
-- name    : BramsonQueueing.Fluid.lemma_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:46.398986+00:00
-- url     : https://prove2.me/theorems/9f713797-6124-4452-b31d-c80f495a96d7
-- title:
--   Lemma 4.13 — Renewal uniform integrability and maximal-increment limits
-- statement:
--   Let $\beta(1),\beta(2),\ldots$ be positive iid random variables with finite mean $m$. Include the first pending renewal in
--   $$B_1(t)=\frac1t\max\left\{n:\sum_{i=1}^{n-1}\beta(i)\le t\right\},\qquad B_2(t)=\frac1t\max\left\{\beta(n):\sum_{i=1}^{n-1}\beta(i)\le t\right\}.$$
--   Then
--   $$\sup_{t\ge1}\mathbb E[B_1(t);B_1(t)\ge M]\longrightarrow0\quad(M\to\infty).$$
--   On the event $G_\beta$ where $n^{-1}\sum_{i=1}^n\beta(i)\to m$, one has $B_2(t)\to0$ as $t\to\infty$. Also
--   $$\mathbb E B_2(t)\longrightarrow0\quad(t\to\infty).$$
--   Only a first moment is assumed. The pathwise limit holds at every sample in the specified strong-law event; the last assertion is the separate expectation limit.
--
--   Differences from the source:
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: possibly infinite nonnegative expectations → ENNReal lower Lebesgue integrals; reason: infinite expectation remains infinite rather than taking the default value of a real integral
--   - encoding: uniform limits or finite suprema → epsilon-threshold statements or one finite bound uniform over the stated indices; reason: these are equivalent and avoid default values for unbounded real suprema
--   - encoding: increments indexed from one and finite maxima on nonexplosive paths → increments indexed from zero and ENNReal suprema; reason: n+1 is the pending index after n increments; infinite exceptional values are retained, while on the strong-law event the maxima are finite
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Lemma 4.13, printed 116 / PDF 124, equations (4.81)–(4.83).

import Definitions.Def_BramsonQueueing_Fluid_Renewal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

theorem lemma_4_13 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : PositiveIID Ω μ) :
    UniformTail μ (fun t : {t : ℝ≥0 // 1 ≤ t} => renewalB1 r t.1) ∧
    (∀ ω, RenewalGood r ω → Tendsto (fun t : ℝ≥0 => renewalB2 r t ω) atTop (𝓝 0)) ∧
    Tendsto (fun t : ℝ≥0 => ∫⁻ ω, renewalB2 r t ω ∂μ) atTop (𝓝 0) := by sorry

end BramsonQueueing.Fluid
