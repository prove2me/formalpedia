-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_proposition_4_4
-- name    : DirKKTBilevel.VP.Supplement.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:28:22.547167+00:00
-- url     : https://prove2.me/theorems/cb4a2538-e3d6-4923-aead-63ef8913d20f
-- title:
--   Proposition 4.4 (used in the proof of Theorem 4.2) — directional derivative of V under directional inner semi-continuity and RCR
-- statement:
--   Let $f,g$ be continuously differentiable. Suppose $S$ is inner semi-continuous at $(\bar x,\bar y)\in\operatorname{gph}S$ in direction $u$ and $\mathcal F$ is RCR-regular at $(\bar x,\bar y)$. Then $V$ is directionally differentiable at $\bar x$ in direction $u$ and
--   $$V'(\bar x;u)=\min_{v\in L(\bar x,\bar y;u)}\nabla f(\bar x,\bar y)(u,v)=\max_{\lambda\in\Lambda(\bar x,\bar y)}\nabla_x\mathcal L(\bar x,\bar y;\lambda)u,$$
--   both extrema attained. This is the sensitivity formula behind Theorems 4.2(ii) and 5.4.
--
--   Differences from the source:
--   - reading: Definitions 2.3 and 4.4 (pp. 6, 13) ask for y_k ∈ Φ(x̄ + t_k u_k) without saying for which k → dirLiminf and IsDirInnerSemicont require y_k ∈ Φ(x̄ + t_k u_k) for all sufficiently large k; reason: this is the Painlevé–Kuratowski convention the paper says it recovers at u = 0 (p. 6); requiring every k would force Φ(x) ≠ ∅ at every point x ≠ x̄, since any point is the first term of some admissible sequence, and the proofs (pp. 16, 18) only use large k.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
--   - encoding: min and max in the derivative formulas → IsLeast / IsGreatest (IsMinOfMins, IsMinOfMaxs): every displayed extremum is attained; reason: the paper writes min/max, i.e. attained extrema; no inf/sup relaxation.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 18, Proposition 4.4

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Proposition 4.4, p. 18: if the solution map `S` is inner semi-continuous at `(x̄, ȳ) ∈ gph S` in
direction `u` and `𝓕` is RCR-regular at `(x̄, ȳ)`, then `V` is directionally differentiable at
`x̄` in direction `u` and `V'(x̄; u) = min_{v ∈ L(x̄,ȳ;u)} ∇f(x̄, ȳ)(u, v)
= max_{λ ∈ Λ(x̄,ȳ)} ∇ₓL(x̄, ȳ; λ)u`, both extrema attained. -/
theorem proposition_4_4 {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : E n) (y : E m) (u : E n)
    (hISC : IsDirInnerSemicont f g x y u) (hRCR : IsRCR g x y) :
    ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
      IsLeast (linVals f g x u y) dV ∧ IsGreatest (lagVals f g x u y) dV := by sorry

end DirKKTBilevel.VP.Supplement
