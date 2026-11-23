-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_theorem_4_3
-- name    : DirKKTBilevel.VP.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:31:06.874996+00:00
-- url     : https://prove2.me/theorems/9d97886b-6870-4779-be17-5a5a2e0c7696
-- title:
--   Theorem 4.3 (companion theorem; not used in the proof of the goal; corrected: Ω_u ⊆ ℝᵐ) — estimates of the directional Clarke subdifferential of V
-- statement:
--   Let $f,g$ be continuously differentiable.
--   1. Under the assumptions of Theorem 4.2(i), for every choice $v(\tilde y)\in\Sigma(\bar x,\tilde y,u)$, one for each $\tilde y\in S(\bar x;u)\cap\Omega_u$ with $\Sigma(\bar x,\tilde y,u)\neq\emptyset$,
--   $$\partial^cV(\bar x;u)\subseteq\operatorname{co}\bigcup_{\tilde y}W(\bar x,\tilde y,u,v(\tilde y)),$$
--   the union running over those $\tilde y$.
--   2. Under the assumptions of Theorem 4.2(ii),
--   $$\partial^cV(\bar x;u)\subseteq W(\bar x,\bar y,u,v)\qquad\forall v\in\Sigma(\bar x,\bar y,u).$$
--   Here $W(x,y,u,v)=\{\nabla_xf(x,y)+\nabla_xg(x,y)^T\lambda_g\mid\lambda_g\in\Lambda(x,y)\cap\{\nabla g(x,y)(u,v)\}^\perp\}$ and $\Sigma$ is (25), formed with $V'(\bar x;u)$, whose existence is part of the conclusion. These estimates are the input of Theorems 5.3 and 5.4.
--
--   Differences from the source:
--   - correction: Definition 4.1 (p. 13) places the compact set Ω_u in ℝⁿ → Ω : Set (E m), a set of lower-level variables in ℝᵐ; reason: Ω_u must meet S(x) ⊆ ℝᵐ, and the proofs of Lemma 4.2 (p. 16) and Proposition 4.3 (p. 17) take limits ỹ ∈ Ω_u of lower-level solutions; ℝⁿ is a dimension slip. No case is excluded.
--   - reading: Definitions 2.3 and 4.4 (pp. 6, 13) ask for y_k ∈ Φ(x̄ + t_k u_k) without saying for which k → dirLiminf and IsDirInnerSemicont require y_k ∈ Φ(x̄ + t_k u_k) for all sufficiently large k; reason: this is the Painlevé–Kuratowski convention the paper says it recovers at u = 0 (p. 6); requiring every k would force Φ(x) ≠ ∅ at every point x ≠ x̄, since any point is the first term of some admissible sequence, and the proofs (pp. 16, 18) only use large k.
--   - reading: Σ(x̄, ỹ, u) (25) and Θ(x̄; u) (27) are defined 'for any x, y, u, suppose V'(x; u) exists' → the conclusion asserts ∃ dV with HasDirDerivAtE V x̄ u dV and states the inclusion with Σ formed from that dV; reason: directional derivatives are unique, so this is the paper's Σ; the existence is supplied by Proposition 4.3/4.4 under the same hypotheses (proof of Theorem 4.2, p. 20).
--   - reading: the first display binds ỹ in the union and then writes '∀v ∈ Σ(x̄, ỹ, u)' after it → for every selection sel with sel(ỹ) ∈ Σ(x̄, ỹ, u) on each ỹ ∈ S(x̄;u) ∩ Ω whose Σ-fibre is nonempty, ∂ᶜV(x̄;u) ⊆ co ⋃ W(x̄, ỹ, u, sel(ỹ)) over those ỹ; reason: the proof (p. 22) shows W(x, y, u, v) does not depend on v ∈ Σ(x, y, u), so any choice per fibre gives co Θ(x̄;u); optimizers with empty Σ-fibre contribute nothing to Θ, and selections always exist, so the statement is not vacuous.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 22, Theorem 4.3

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Theorem 4.3, p. 22: (i) under the assumptions of Theorem 4.2(i),
`∂ᶜV(x̄; u) ⊆ co ⋃_{ỹ ∈ S(x̄;u) ∩ Ω} W(x̄, ỹ, u, v(ỹ))` for every choice `v(ỹ) ∈ Σ(x̄, ỹ, u)` (made
for each `ỹ` whose `Σ(x̄, ỹ, u)` is nonempty, the union running over those `ỹ`); (ii) under the
assumptions of Theorem 4.2(ii), `∂ᶜV(x̄; u) ⊆ W(x̄, ȳ, u, v)` for every `v ∈ Σ(x̄, ȳ, u)`. -/
theorem theorem_4_3 {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x u : E n) :
    (∀ Ω : Set (E m), IsRestrInfCompactDir f g x u Ω → (∀ y ∈ solMap f g x, IsRCR g x y) →
        (∀ y ∈ solMap f g x, IsRSDir g x y u) →
        ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
          ∀ sel : E m → E m,
            (∀ y ∈ dirSol f g x u ∩ Ω, (sigmaSet f g x y u dV).Nonempty →
              sel y ∈ sigmaSet f g x y u dV) →
            dirClarke (valueFn f g) x u ⊆
              convexHull ℝ (⋃ y ∈ {y | y ∈ dirSol f g x u ∩ Ω ∧ (sigmaSet f g x y u dV).Nonempty},
                Wset f g x y u (sel y))) ∧
    (∀ y : E m, IsDirInnerSemicont f g x y u → IsRCR g x y →
        ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
          ∀ v ∈ sigmaSet f g x y u dV, dirClarke (valueFn f g) x u ⊆ Wset f g x y u v) := by sorry

end DirKKTBilevel.VP.Supplement
