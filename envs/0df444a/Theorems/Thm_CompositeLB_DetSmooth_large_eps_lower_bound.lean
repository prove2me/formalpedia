-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_large_eps_lower_bound
-- name    : CompositeLB.DetSmooth.large_eps_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:00.865981+00:00
-- url     : https://prove2.me/theorems/394c4edf-589b-47c9-a1c5-08faac799e68
-- title:
--   Appendix B.3, p. 16 — the linear construction forces m queries
-- statement:
--   Let $m\ge2$, $d\ge m$, $\epsilon>0$, and let $A$ be a deterministic exact gradient and prox oracle algorithm. There are $m$ convex components that are $1$-smooth on the unit ball, an exact oracle, and a minimizer $x^*$ such that every one of the first $m-1$ query points satisfies
--
--   $$F(x_n)-F(x^*)\ge\epsilon.$$
--
--   The components are linear or zero, so this supplies the large-accuracy-parameter branch of the lower-bound construction.
--
--   **Formalization Note** The dimension hypothesis allows a unit vector orthogonal to the first $m-1$ queries. The paper writes $F(v)=-2\epsilon$ for positive linear components; the minimum is instead attained at $-v$, with value at most $-2\epsilon$. The goal theorem uses a smaller dimension for sufficiently large $\epsilon$, as recorded in the moderation notes.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Appendix B.3, p. 16, paragraph beginning “This proves the lower bound”

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Model

namespace CompositeLB.DetSmooth

/-- Appendix B.3, p. 16: the linear-component construction keeps each of
the first `m-1` query points at least `ε` above the constrained optimum. -/
theorem large_eps_lower_bound (m d : ℕ) (ε : ℝ)
    (hm : 2 ≤ m) (hmd : m ≤ d) (hε : 0 < ε) (A : CompositeLB.DetLip.DetAlg m d) :
    ∃ (f : Fin m → CompositeLB.DetLip.E d → ℝ) (O : CompositeLB.DetLip.Oracle m d),
      (∀ i, ConvexOn ℝ (Metric.closedBall (0 : CompositeLB.DetLip.E d) 1) (f i) ∧
        IsSmoothOn 1 (f i) (Metric.closedBall (0 : CompositeLB.DetLip.E d) 1)) ∧
      IsValidOracle f (Metric.closedBall (0 : CompositeLB.DetLip.E d) 1) O ∧
      ∃ xstar ∈ Metric.closedBall (0 : CompositeLB.DetLip.E d) 1,
        (∀ y ∈ Metric.closedBall (0 : CompositeLB.DetLip.E d) 1,
          CompositeLB.DetLip.avgF f xstar ≤ CompositeLB.DetLip.avgF f y) ∧
        ∀ n : ℕ, n + 1 ≤ m - 1 →
          ε ≤ CompositeLB.DetLip.avgF f (CompositeLB.DetLip.query A O n).pt - CompositeLB.DetLip.avgF f xstar := by sorry

end CompositeLB.DetSmooth
