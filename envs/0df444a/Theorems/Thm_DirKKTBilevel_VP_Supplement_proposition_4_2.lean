-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_proposition_4_2
-- name    : DirKKTBilevel.VP.Supplement.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:25:29.391273+00:00
-- url     : https://prove2.me/theorems/497c4e85-f31a-4736-b50c-3365445e7a3d
-- title:
--   Proposition 4.2 (used in the proof of Theorem 4.2) — directional RS implies directional MSCQ of g(x, y) ≤ 0
-- statement:
--   Suppose the feasible map $\mathcal F(x)=\{y\mid g(x,y)\le0\}$ satisfies Robinson stability at $(\bar x,\bar y)\in\operatorname{gph}\mathcal F$ in direction $u$. Then for every $v\in\mathbb R^m$ the system $g(x,y)\le0$ satisfies the directional MSCQ at $(\bar x,\bar y)$ in direction $(u,v)$:
--   $$\operatorname{dist}\big((x,y),g^{-1}(\mathbb R^p_-)\big)\le\kappa\|g_+(x,y)\|\quad\forall (x,y)\in(\bar x,\bar y)+V_{\varepsilon,\delta}(u,v)$$
--   for some $\kappa,\varepsilon,\delta>0$. It lets the subgradient estimate of Theorem 4.2 use the normal-cone calculus of the constraint system at nearby optimizers.
--
--   Differences from the source:
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 15, Proposition 4.2

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Proposition 4.2, p. 15: if the feasible map `𝓕(x) = {y | g(x, y) ≤ 0}` satisfies RS at
`(x̄, ȳ) ∈ gph 𝓕` in direction `u`, then the system `g(x, y) ≤ 0` satisfies the directional MSCQ at
`(x̄, ȳ)` in direction `(u, v)` for every `v ∈ ℝᵐ`. -/
theorem proposition_4_2 {n m p : ℕ} (g : Z n m → E p) (hg : ContDiff ℝ 1 g)
    (x : E n) (y : E m) (u : E n) (hRS : IsRSDir g x y u) :
    ∀ v : E m, DirMSCQ g (WithLp.toLp 2 (x, y) : Z n m) (WithLp.toLp 2 (u, v)) := by sorry

end DirKKTBilevel.VP.Supplement
