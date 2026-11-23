-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_theorem_5_2
-- name    : DirKKTBilevel.VP.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:33:06.209542+00:00
-- url     : https://prove2.me/theorems/7a0adccd-7e41-4904-887c-51bdccec7bad
-- title:
--   Theorem 5.2 (companion theorem; not used in the proof of the goal) — directional KKT conditions for (BP) under directional quasi-normality
-- statement:
--   Let $(\bar x,\bar y)$ be a local minimizer of (BP) with $F,f,g,G$ continuously differentiable. Suppose $V$ is directionally Lipschitz continuous and directionally differentiable at $\bar x$ in direction $u$, and $(u,v)\in C(\bar x,\bar y)$. Suppose the directional quasi-normality holds at $(\bar x,\bar y)$ in direction $(u,v)$: there is no nonzero $(\alpha,\nu_g,\nu_G)\in\mathbb R^{1+p+q}_+$ with
--   $$0\in\alpha\nabla f(\bar x,\bar y)-\alpha\partial^cV(\bar x;u)\times\{0\}+\nabla g(\bar x,\bar y)^T\nu_g+\nabla G(\bar x,\bar y)^T\nu_G,\qquad(35)$$
--   $\nu_g\perp g(\bar x,\bar y)$, $\nu_g\perp\nabla g(\bar x,\bar y)(u,v)$, $\nu_G\perp G(\bar x,\bar y)$, $\nu_G\perp\nabla G(\bar x,\bar y)(u,v)$ (36), and sequences $t_k\downarrow0$, $(u_k,v_k)\to(u,v)$ with $f-V>0$ at $(\bar x+t_ku_k,\bar y+t_kv_k)$ if $\alpha>0$ (37), and $g_i>0$ (resp. $G_i>0$) there for active $i$ with $(\nu_g)_i>0$ (resp. $(\nu_G)_i>0$) (38). Then:
--   1. the directional KKT condition of Theorem 5.1 holds (with $\partial(-V)(\bar x;u)$);
--   2. moreover there is $(\lambda_V,\lambda_g,\lambda_G)$ with
--   $$0\in\nabla F(\bar x,\bar y)+\lambda_V\nabla f(\bar x,\bar y)-\lambda_V\partial^cV(\bar x;u)\times\{0\}+\nabla g(\bar x,\bar y)^T\lambda_g+\nabla G(\bar x,\bar y)^T\lambda_G,$$
--   $\lambda_V\ge0$, $0\le\lambda_g\perp g(\bar x,\bar y)$, $\lambda_g\perp\nabla g(\bar x,\bar y)(u,v)$, $0\le\lambda_G\perp G(\bar x,\bar y)$, $\lambda_G\perp\nabla G(\bar x,\bar y)(u,v)$.
--
--   The theorem replaces the calmness hypothesis of Theorem 5.1 by a condition on the problem data.
--
--   **Formalization Note** The hypotheses on $V$ and the critical cone are those of the published Theorem 5.1 (`hLip`, `hdiff` with $V'(\bar x;u)=dV$, `criticalConeVP`).
--
--   Differences from the source:
--   - encoding: t_k ↓ 0 → t k > 0 for all k and t → 0; reason: a decreasing subsequence can always be extracted; the same encoding as the published base mission.
--   - encoding: λ ⊥ w for vectors → Σ_i λ_i w_i = 0; reason: the inner product of ℝᵖ; the same encoding as the published base mission.
--   - encoding: (37): α(f − V) > 0 if α > 0; (u_k, v_k) → (u, v) → 0 < α → V(x̄ + t_k u_k) < f(x̄ + t_k u_k, ȳ + t_k v_k) in EReal, with u_k → u and v_k → v separately; reason: for α > 0 the two inequalities are equivalent and EReal avoids a junk toReal; componentwise convergence is convergence in the product.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 25, Theorem 5.2

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Theorem 5.2, p. 25: let `(x̄, ȳ)` be a local minimizer of (BP), let `V` be directionally
Lipschitz continuous and directionally differentiable at `x̄` in direction `u` (with
`V'(x̄; u) = dV`), let `(u, v) ∈ C(x̄, ȳ)`, and let the directional quasi-normality (35)–(38) hold
at `(x̄, ȳ)` in direction `(u, v)`. Then the directional KKT condition of Theorem 5.1 holds, and
moreover there are `(λ_V, λ_g, λ_G)` with
`0 ∈ ∇F(x̄,ȳ) + λ_V∇f(x̄,ȳ) − λ_V∂ᶜV(x̄; u) × {0} + ∇g(x̄,ȳ)ᵀλ_g + ∇G(x̄,ȳ)ᵀλ_G`, `λ_V ≥ 0`,
`0 ≤ λ_g ⊥ g(x̄,ȳ)`, `λ_g ⊥ ∇g(x̄,ȳ)(u,v)`, `0 ≤ λ_G ⊥ G(x̄,ȳ)`, `λ_G ⊥ ∇G(x̄,ȳ)(u,v)`. -/
theorem theorem_5_2 {n m p q : ℕ} (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (hF : ContDiff ℝ 1 F) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hG : ContDiff ℝ 1 G)
    (x : E n) (y : E m) (u : E n) (v : E m) (dV : ℝ)
    (hmin : IsLocalMinBP F f g G x y)
    (hLip : DirLipschitzAtEReal (valueFn f g) x u)
    (hdiff : HasDirDerivAt (fun x' => (valueFn f g x').toReal) x u dV)
    (hcrit : criticalConeVP F f g G x y dV (WithLp.toLp 2 (u, v)))
    (hQN : IsDirQNVP f g G x y u v (dirClarke (valueFn f g) x u)) :
    DirKKTVP F f g G x y u v ∧
      DirKKTVPWith F f g G x y u v (dirClarke (valueFn f g) x u) := by sorry

end DirKKTBilevel.VP.Supplement
