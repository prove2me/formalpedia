-- Prove2me | Theorems.Thm_BRWMinimum_Law_global_min_tail
-- name    : BRWMinimum.Law.global_min_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:16:46.510834+00:00
-- url     : https://prove2.me/theorems/4b72260d-bcf1-46e0-8858-4ba763f63313
-- title:
--   §3, display after Corollary 3.4 — 𝐏(∃ u ∈ 𝕋 : V(u) ≤ −y) ≤ e^{−y} for y ≥ 0
-- statement:
--   Let $(V(u),u\in\mathbb T)$ be a branching random walk started at $0$ in the boundary case (1.1). For every $y\ge0$,
--   $$\mathbf P\big(\exists\,u\in\mathbb T:\ V(u)\le-y\big)\le e^{-y}.$$
--
--   The overall minimum of the branching random walk over all generations therefore has an exponential lower tail. The bound is used in Corollary 3.5 and at the start of the proof of Proposition 4.1.
--
--   **Formalization Note** The page writes the bound as the end of a chain of (in)equalities obtained from the many-to-one lemma; the formal statement is the end-to-end inequality, for $y\ge0$ as the paper uses it (at $y=0$ the root itself gives probability $1$). Only (1.1) is assumed.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 16, §3, display after Corollary 3.4

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- §3, display after Corollary 3.4: `P(∃ u ∈ 𝕋 : V(u) ≤ −y) ≤ e^{−y}` for `y ≥ 0`. -/
theorem global_min_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (y : ℝ) (hy : 0 ≤ y) :
    P {ω | ∃ u : List ℕ, InTree ξ u ω ∧ pos ξ 0 u ω ≤ -y} ≤ ENNReal.ofReal (Real.exp (-y)) := by sorry

end BRWMinimum.Law
