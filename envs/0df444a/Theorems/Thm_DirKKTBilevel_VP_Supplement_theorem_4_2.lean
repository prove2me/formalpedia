-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_theorem_4_2
-- name    : DirKKTBilevel.VP.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:29:07.848029+00:00
-- url     : https://prove2.me/theorems/3a7a7186-a966-4ed9-aab9-feffa50db016
-- title:
--   Theorem 4.2 (companion theorem; not used in the proof of the goal; corrected: Ω_u ⊆ ℝᵐ) — upper estimates of the directional subdifferential of V
-- statement:
--   Let $f,g$ be continuously differentiable and $u\in\mathbb R^n$.
--   1. Suppose the restricted inf-compactness holds at $\bar x$ in direction $u$ with compact $\Omega_u\subseteq\mathbb R^m$, and $\mathcal F$ is RCR-regular at and satisfies RS in direction $u$ at each $(\bar x,y)\in\operatorname{gph}S$. Then $V$ is directionally Lipschitz continuous at $\bar x$ in direction $u$, $V'(\bar x;u)$ exists, and
--   $$\emptyset\neq\partial V(\bar x;u)\subseteq\Theta(\bar x;u)\qquad(26)$$
--   with $\Theta$ from (27).
--   2. Suppose some $\bar y\in S(\bar x)$ has $S$ inner semi-continuous at $(\bar x,\bar y)$ in direction $u$ and $\mathcal F$ RCR-regular at $(\bar x,\bar y)$. Then $V$ is directionally Lipschitz at $\bar x$ in direction $u$, $V'(\bar x;u)$ exists, and
--   $$\emptyset\neq\partial V(\bar x;u)\subseteq\bigcup_{v\in\Sigma(\bar x,\bar y,u)}\big\{\nabla_xf(\bar x,\bar y)+\nabla_xg(\bar x,\bar y)^T\lambda_g\ \big|\ \lambda_g\in\Lambda(\bar x,\bar y)\cap\{\nabla g(\bar x,\bar y)(u,v)\}^\perp\big\}.$$
--   Here $\partial V(\bar x;u)$ is the directional limiting subdifferential (Definition 2.6) and $\Sigma$ is (25). The estimates express the value function's subgradients through lower-level multipliers.
--
--   Differences from the source:
--   - correction: Definition 4.1 (p. 13) places the compact set Ω_u in ℝⁿ → Ω : Set (E m), a set of lower-level variables in ℝᵐ; reason: Ω_u must meet S(x) ⊆ ℝᵐ, and the proofs of Lemma 4.2 (p. 16) and Proposition 4.3 (p. 17) take limits ỹ ∈ Ω_u of lower-level solutions; ℝⁿ is a dimension slip. No case is excluded.
--   - reading: Definitions 2.3 and 4.4 (pp. 6, 13) ask for y_k ∈ Φ(x̄ + t_k u_k) without saying for which k → dirLiminf and IsDirInnerSemicont require y_k ∈ Φ(x̄ + t_k u_k) for all sufficiently large k; reason: this is the Painlevé–Kuratowski convention the paper says it recovers at u = 0 (p. 6); requiring every k would force Φ(x) ≠ ∅ at every point x ≠ x̄, since any point is the first term of some admissible sequence, and the proofs (pp. 16, 18) only use large k.
--   - reading: Σ(x̄, ỹ, u) (25) and Θ(x̄; u) (27) are defined 'for any x, y, u, suppose V'(x; u) exists' → the conclusion asserts ∃ dV with HasDirDerivAtE V x̄ u dV and states the inclusion with Σ formed from that dV; reason: directional derivatives are unique, so this is the paper's Σ; the existence is supplied by Proposition 4.3/4.4 under the same hypotheses (proof of Theorem 4.2, p. 20).
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 19, Theorem 4.2

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Theorem 4.2, pp. 19–20: (i) under the restricted inf-compactness at `x̄` in direction `u` with
compact `Ω`, RCR-regularity of `𝓕` at each `(x̄, y) ∈ gph S` and RS at each `(x̄, y) ∈ gph S` in
direction `u`, `V` is directionally Lipschitz continuous at `x̄` in direction `u` and
`∅ ≠ ∂V(x̄; u) ⊆ Θ(x̄; u)` (26)–(27); (ii) if some `ȳ ∈ S(x̄)` has `S` inner semi-continuous at
`(x̄, ȳ)` in direction `u` and `𝓕` is RCR-regular at `(x̄, ȳ)`, then `V` is directionally
Lipschitz at `x̄` in direction `u` and
`∅ ≠ ∂V(x̄; u) ⊆ ⋃_{v ∈ Σ(x̄,ȳ,u)} {∇ₓf(x̄,ȳ) + ∇ₓg(x̄,ȳ)ᵀλ_g | λ_g ∈ Λ(x̄,ȳ) ∩ {∇g(x̄,ȳ)(u,v)}^⊥}`.
`Σ` (25) is formed with `V'(x̄; u)`, whose existence is part of each conclusion. -/
theorem theorem_4_2 {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x u : E n) :
    (∀ Ω : Set (E m), IsRestrInfCompactDir f g x u Ω → (∀ y ∈ solMap f g x, IsRCR g x y) →
        (∀ y ∈ solMap f g x, IsRSDir g x y u) →
        DirLipschitzAtEReal (valueFn f g) x u ∧
          ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
            (dirSubdiff (valueFn f g) x u).Nonempty ∧
            dirSubdiff (valueFn f g) x u ⊆ Theta f g x u Ω dV) ∧
    (∀ y : E m, IsDirInnerSemicont f g x y u → IsRCR g x y →
        DirLipschitzAtEReal (valueFn f g) x u ∧
          ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
            (dirSubdiff (valueFn f g) x u).Nonempty ∧
            dirSubdiff (valueFn f g) x u ⊆
              ⋃ v ∈ sigmaSet f g x y u dV, Wset f g x y u v) := by sorry

end DirKKTBilevel.VP.Supplement
