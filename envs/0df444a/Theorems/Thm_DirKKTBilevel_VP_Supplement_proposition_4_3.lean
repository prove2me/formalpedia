-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_proposition_4_3
-- name    : DirKKTBilevel.VP.Supplement.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:27:07.489442+00:00
-- url     : https://prove2.me/theorems/4b21cbf1-1d64-4185-be28-323c9990ae4e
-- title:
--   Proposition 4.3 (used in the proof of Theorem 4.2; corrected: Ω_u ⊆ ℝᵐ) — directional derivative of V under RCR, RS and restricted inf-compactness
-- statement:
--   Let $f,g$ be continuously differentiable. Assume $\mathcal F$ is RCR-regular at each $(\bar x,y)\in\operatorname{gph}S$, the restricted inf-compactness holds at $\bar x$ in direction $u$ (compact $\Omega_u\subseteq\mathbb R^m$), and RS holds at each $(\bar x,y)\in\operatorname{gph}S$ in direction $u$. Then $V$ is directionally differentiable at $\bar x$ in direction $u$ and
--   $$V'(\bar x;u)=\min_{y\in S(\bar x;u)}\ \min_{v\in L(\bar x,y;u)}\nabla f(\bar x,y)(u,v)=\min_{y\in S(\bar x;u)}\ \max_{\lambda\in\Lambda(\bar x,y)}\nabla_x\mathcal L(\bar x,y;\lambda)u,\qquad(17)$$
--   where every inner minimum and maximum is attained for each $y\in S(\bar x;u)$ and both outer minima are attained. This is the sensitivity formula behind Theorems 4.2 and 5.3.
--
--   Differences from the source:
--   - correction: Definition 4.1 (p. 13) places the compact set Ω_u in ℝⁿ → Ω : Set (E m), a set of lower-level variables in ℝᵐ; reason: Ω_u must meet S(x) ⊆ ℝᵐ, and the proofs of Lemma 4.2 (p. 16) and Proposition 4.3 (p. 17) take limits ỹ ∈ Ω_u of lower-level solutions; ℝⁿ is a dimension slip. No case is excluded.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
--   - encoding: min and max in the derivative formulas → IsLeast / IsGreatest (IsMinOfMins, IsMinOfMaxs): every displayed extremum is attained; reason: the paper writes min/max, i.e. attained extrema; no inf/sup relaxation.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 16, Proposition 4.3

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Proposition 4.3, p. 16: assume `𝓕` is RCR-regular at each `(x̄, y) ∈ gph S`, the restricted
inf-compactness holds at `x̄` in direction `u` (compact set `Ω`), and RS holds at each
`(x̄, y) ∈ gph S` in direction `u`. Then `V` is directionally differentiable at `x̄` in direction
`u` and (17): `V'(x̄; u) = min_{y ∈ S(x̄;u)} min_{v ∈ L(x̄,y;u)} ∇f(x̄, y)(u, v)
= min_{y ∈ S(x̄;u)} max_{λ ∈ Λ(x̄,y)} ∇ₓL(x̄, y; λ)u`, every extremum attained. -/
theorem proposition_4_3 {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x u : E n) (Ω : Set (E m))
    (hRCR : ∀ y ∈ solMap f g x, IsRCR g x y) (hRIC : IsRestrInfCompactDir f g x u Ω)
    (hRS : ∀ y ∈ solMap f g x, IsRSDir g x y u) :
    ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
      IsMinOfMins (dirSol f g x u) (linVals f g x u) dV ∧
      IsMinOfMaxs (dirSol f g x u) (lagVals f g x u) dV := by sorry

end DirKKTBilevel.VP.Supplement
