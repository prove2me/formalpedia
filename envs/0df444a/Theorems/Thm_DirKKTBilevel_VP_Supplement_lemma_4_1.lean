-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_lemma_4_1
-- name    : DirKKTBilevel.VP.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:21:43.016657+00:00
-- url     : https://prove2.me/theorems/c1f4fb66-3b62-4aa3-9385-25757d9c9a1d
-- title:
--   Lemma 4.1 (used in the proof of Theorem 4.1) — D₊𝓕(x̄, ȳ; u) = L(x̄, ȳ; u) under directional RS or under RCR
-- statement:
--   Let $\bar y\in\mathcal F(\bar x)=\{y\mid g(\bar x,y)\le0\}$ and $u\in\mathbb R^n$. Suppose either that the feasible map $\mathcal F$ satisfies Robinson stability at $(\bar x,\bar y)$ in direction $u$, or that $D_+\mathcal F(\bar x,\bar y;u)\neq\emptyset$ and $\mathcal F$ is RCR-regular at $(\bar x,\bar y)$. Then the lower Dini derivative of the feasible map equals the $y$-projection of the linearization cone:
--   $$D_+\mathcal F(\bar x,\bar y;u)=L(\bar x,\bar y;u).$$
--   The lemma identifies the first-order feasible velocities of the lower-level constraint system, and is the step from which Lemma 4.2 and Proposition 4.3 compute $V'(\bar x;u)$.
--
--   Differences from the source:
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Lemma 4.1, p. 15: let `ȳ ∈ 𝓕(x̄)`. If either `𝓕` satisfies RS at `(x̄, ȳ)` in direction `u`, or
`D₊𝓕(x̄, ȳ; u) ≠ ∅` and `𝓕` is RCR-regular at `(x̄, ȳ)`, then `D₊𝓕(x̄, ȳ; u) = L(x̄, ȳ; u)`. -/
theorem lemma_4_1 {n m p : ℕ} (g : Z n m → E p) (hg : ContDiff ℝ 1 g)
    (x : E n) (y : E m) (u : E n) (hy : y ∈ feasLL g x)
    (h : IsRSDir g x y u ∨ ((diniFeas g x y u).Nonempty ∧ IsRCR g x y)) :
    diniFeas g x y u = linLL g x y u := by sorry

end DirKKTBilevel.VP.Supplement
