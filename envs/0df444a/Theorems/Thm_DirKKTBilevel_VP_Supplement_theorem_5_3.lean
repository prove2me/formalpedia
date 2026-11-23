-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_theorem_5_3
-- name    : DirKKTBilevel.VP.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:34:02.576806+00:00
-- url     : https://prove2.me/theorems/3a38b210-6205-445d-8b4a-0eeb5b25d1a8
-- title:
--   Theorem 5.3 (companion theorem; not used in the proof of the goal; corrected: Ω_u ⊆ ℝᵐ) — directional KKT conditions in terms of the data under RCR, RS and restricted inf-compactness
-- statement:
--   Let $(\bar x,\bar y)$ be a local minimizer of (BP), with $F,f,g,G$ continuously differentiable, and $u\in\mathbb R^n$. Suppose $\mathcal F$ is RCR-regular at and satisfies RS in direction $u$ at each $(\bar x,y)\in\operatorname{gph}S$, and the restricted inf-compactness holds at $\bar x$ in direction $u$ with compact $\Omega_u\subseteq\mathbb R^m$. Then $V$ is directionally Lipschitz continuous and directionally differentiable at $\bar x$ in direction $u$ with
--   $$V'(\bar x;u)=\min_{y\in S(\bar x;u)}\max_{\lambda\in\Lambda(\bar x,y)}\nabla_x\mathcal L(\bar x,y;\lambda)u,\qquad\partial V(\bar x;u)\subseteq\Theta(\bar x;u),$$
--   extrema attained, $\Theta$ as in (27). If moreover $(u,v)\in C(\bar x,\bar y)$ and the directional quasi-normality of Theorem 5.2 holds with $\partial^cV(\bar x;u)$ replaced by $\operatorname{co}\Theta(\bar x;u)$, then the directional KKT condition holds and the conclusion of Theorem 5.2 holds with $\partial^cV(\bar x;u)$ replaced by $\operatorname{co}\Theta(\bar x;u)$.
--
--   The sensitivity conclusions need no quasi-normality; only the KKT conclusions do.
--
--   Differences from the source:
--   - correction: Definition 4.1 (p. 13) places the compact set Ω_u in ℝⁿ → Ω : Set (E m), a set of lower-level variables in ℝᵐ; reason: Ω_u must meet S(x) ⊆ ℝᵐ, and the proofs of Lemma 4.2 (p. 16) and Proposition 4.3 (p. 17) take limits ỹ ∈ Ω_u of lower-level solutions; ℝⁿ is a dimension slip. No case is excluded.
--   - reading: Σ(x̄, ỹ, u) (25) and Θ(x̄; u) (27) are defined 'for any x, y, u, suppose V'(x; u) exists' → the conclusion asserts ∃ dV with HasDirDerivAtE V x̄ u dV and states the inclusion with Σ formed from that dV; reason: directional derivatives are unique, so this is the paper's Σ; the existence is supplied by Proposition 4.3/4.4 under the same hypotheses (proof of Theorem 4.2, p. 20).
--   - encoding: t_k ↓ 0 → t k > 0 for all k and t → 0; reason: a decreasing subsequence can always be extracted; the same encoding as the published base mission.
--   - encoding: λ ⊥ w for vectors → Σ_i λ_i w_i = 0; reason: the inner product of ℝᵖ; the same encoding as the published base mission.
--   - encoding: (37): α(f − V) > 0 if α > 0; (u_k, v_k) → (u, v) → 0 < α → V(x̄ + t_k u_k) < f(x̄ + t_k u_k, ȳ + t_k v_k) in EReal, with u_k → u and v_k → v separately; reason: for α > 0 the two inequalities are equivalent and EReal avoids a junk toReal; componentwise convergence is convergence in the product.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
--   - encoding: min and max in the derivative formulas → IsLeast / IsGreatest (IsMinOfMins, IsMinOfMaxs): every displayed extremum is attained; reason: the paper writes min/max, i.e. attained extrema; no inf/sup relaxation.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 25, Theorem 5.3

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Theorem 5.3, pp. 25–26: let `(x̄, ȳ)` be a local minimizer of (BP), let `𝓕` be RCR-regular at
each `(x̄, y) ∈ gph S` and satisfy RS at each `(x̄, y) ∈ gph S` in direction `u`, and let the
restricted inf-compactness hold at `x̄` in direction `u` with compact `Ω`. Then `V` is
directionally Lipschitz continuous and directionally differentiable at `x̄` in direction `u`,
`V'(x̄; u) = min_{y ∈ S(x̄;u)} max_{λ ∈ Λ(x̄,y)} ∇ₓL(x̄, y; λ)u` (attained) and
`∂V(x̄; u) ⊆ Θ(x̄; u)`. If moreover `(u, v) ∈ C(x̄, ȳ)` and the directional quasi-normality of
Theorem 5.2 holds with `∂ᶜV(x̄; u)` replaced by `co Θ(x̄; u)`, then the directional KKT condition
and Theorem 5.2 hold with `∂ᶜV(x̄; u)` replaced by `co Θ(x̄; u)`. -/
theorem theorem_5_3 {n m p q : ℕ} (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (hF : ContDiff ℝ 1 F) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hG : ContDiff ℝ 1 G)
    (x : E n) (y : E m) (u : E n) (Ω : Set (E m))
    (hmin : IsLocalMinBP F f g G x y)
    (hRCR : ∀ y' ∈ solMap f g x, IsRCR g x y')
    (hRS : ∀ y' ∈ solMap f g x, IsRSDir g x y' u)
    (hRIC : IsRestrInfCompactDir f g x u Ω) :
    DirLipschitzAtEReal (valueFn f g) x u ∧
      ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
        IsMinOfMaxs (dirSol f g x u) (lagVals f g x u) dV ∧
        dirSubdiff (valueFn f g) x u ⊆ Theta f g x u Ω dV ∧
        ∀ v : E m, criticalConeVP F f g G x y dV (WithLp.toLp 2 (u, v)) →
          IsDirQNVP f g G x y u v (convexHull ℝ (Theta f g x u Ω dV)) →
          DirKKTVP F f g G x y u v ∧
            DirKKTVPWith F f g G x y u v (convexHull ℝ (Theta f g x u Ω dV)) := by sorry

end DirKKTBilevel.VP.Supplement
