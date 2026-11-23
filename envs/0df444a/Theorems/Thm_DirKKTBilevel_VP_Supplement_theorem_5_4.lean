-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_theorem_5_4
-- name    : DirKKTBilevel.VP.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:34:46.292024+00:00
-- url     : https://prove2.me/theorems/fed7828a-2f9a-479f-ad11-02e1d754b380
-- title:
--   Theorem 5.4 (companion theorem; not used in the proof of the goal) — directional KKT conditions under directional inner semi-continuity and RCR
-- statement:
--   Let $(\bar x,\bar y)$ be a local minimizer of (BP) with $F,f,g,G$ continuously differentiable. Suppose $\mathcal F$ is RCR-regular at $(\bar x,\bar y)$ and $S$ is inner semi-continuous at $(\bar x,\bar y)$ in direction $u$. Then $V$ is directionally Lipschitz continuous and directionally differentiable at $\bar x$ in direction $u$ and $V'(\bar x;u)=\max_{\lambda\in\Lambda(\bar x,\bar y)}\nabla_x\mathcal L(\bar x,\bar y;\lambda)u$ (attained). Suppose further that $(u,v)\in C(\bar x,\bar y)$ and there is no nonzero $(\alpha,\nu_g,\nu_G)$ with
--   $$0\in\alpha\nabla f(\bar x,\bar y)-\alpha W(\bar x,\bar y,u,v)\times\{0\}+\nabla g(\bar x,\bar y)^T\nu_g+\nabla G(\bar x,\bar y)^T\nu_G,$$
--   $\alpha\ge0$, $0\le\nu_g\perp g(\bar x,\bar y)$, $\nu_g\perp\nabla g(\bar x,\bar y)(u,v)$, $0\le\nu_G\perp G(\bar x,\bar y)$, $\nu_G\perp\nabla G(\bar x,\bar y)(u,v)$, together with sequences $t_k\downarrow0$, $(u_k,v_k)\to(u,v)$ satisfying (37)–(38). Then there is $(\lambda_V,\lambda_g,\lambda_G,\lambda)\in\mathbb R^{1+p+q+p}$ with, at $(\bar x,\bar y)$,
--   $$0=\nabla_xF-\lambda_V\nabla_xg^T\lambda+\nabla_xg^T\lambda_g+\nabla_xG^T\lambda_G,\qquad 0=\nabla_yF+\lambda_V\nabla_yf+\nabla_yg^T\lambda_g+\nabla_yG^T\lambda_G,$$
--   $\lambda_V\ge0$, $0\le\lambda_g\perp g$, $\lambda_g\perp\nabla g(u,v)$, $0\le\lambda_G\perp G$, $\lambda_G\perp\nabla G(u,v)$, and
--   $$0=\nabla_yf+\nabla_yg^T\lambda,\qquad 0\le\lambda\perp g,\qquad\lambda\perp\nabla g(u,v).$$
--   This is the most explicit KKT system of the paper: it involves only first derivatives of the data and lower-level multipliers.
--
--   Differences from the source:
--   - reading: Definitions 2.3 and 4.4 (pp. 6, 13) ask for y_k ∈ Φ(x̄ + t_k u_k) without saying for which k → dirLiminf and IsDirInnerSemicont require y_k ∈ Φ(x̄ + t_k u_k) for all sufficiently large k; reason: this is the Painlevé–Kuratowski convention the paper says it recovers at u = 0 (p. 6); requiring every k would force Φ(x) ≠ ∅ at every point x ≠ x̄, since any point is the first term of some admissible sequence, and the proofs (pp. 16, 18) only use large k.
--   - encoding: t_k ↓ 0 → t k > 0 for all k and t → 0; reason: a decreasing subsequence can always be extracted; the same encoding as the published base mission.
--   - encoding: λ ⊥ w for vectors → Σ_i λ_i w_i = 0; reason: the inner product of ℝᵖ; the same encoding as the published base mission.
--   - encoding: (37): α(f − V) > 0 if α > 0; (u_k, v_k) → (u, v) → 0 < α → V(x̄ + t_k u_k) < f(x̄ + t_k u_k, ȳ + t_k v_k) in EReal, with u_k → u and v_k → v separately; reason: for α > 0 the two inequalities are equivalent and EReal avoids a junk toReal; componentwise convergence is convergence in the product.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
--   - encoding: min and max in the derivative formulas → IsLeast / IsGreatest (IsMinOfMins, IsMinOfMaxs): every displayed extremum is attained; reason: the paper writes min/max, i.e. attained extrema; no inf/sup relaxation.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 26, Theorem 5.4

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Theorem 5.4, p. 26: let `(x̄, ȳ)` be a local minimizer of (BP), let `𝓕` be RCR-regular at
`(x̄, ȳ)` and `S` inner semi-continuous at `(x̄, ȳ)` in direction `u`. Then `V` is directionally
Lipschitz continuous and directionally differentiable at `x̄` in direction `u` and
`V'(x̄; u) = max_{λ ∈ Λ(x̄,ȳ)} ∇ₓL(x̄, ȳ; λ)u` (attained). If moreover `(u, v) ∈ C(x̄, ȳ)` and no
nonzero `(α, ν_g, ν_G)` satisfies the `W(x̄, ȳ, u, v)`-form of (35)–(36) together with sequences
(37)–(38), then there is `(λ_V, λ_g, λ_G, λ) ∈ ℝ^{1+p+q+p}` with
`0 = ∇ₓF − λ_V∇ₓgᵀλ + ∇ₓgᵀλ_g + ∇ₓGᵀλ_G`, `0 = ∇_yF + λ_V∇_yf + ∇_ygᵀλ_g + ∇_yGᵀλ_G`,
`λ_V ≥ 0`, `0 ≤ λ_g ⊥ g`, `λ_g ⊥ ∇g(u,v)`, `0 ≤ λ_G ⊥ G`, `λ_G ⊥ ∇G(u,v)`,
`0 = ∇_yf + ∇_ygᵀλ`, `0 ≤ λ ⊥ g`, `λ ⊥ ∇g(u,v)`, all at `(x̄, ȳ)`. -/
theorem theorem_5_4 {n m p q : ℕ} (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (hF : ContDiff ℝ 1 F) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hG : ContDiff ℝ 1 G)
    (x : E n) (y : E m) (u : E n)
    (hmin : IsLocalMinBP F f g G x y) (hRCR : IsRCR g x y)
    (hISC : IsDirInnerSemicont f g x y u) :
    DirLipschitzAtEReal (valueFn f g) x u ∧
      ∃ dV : ℝ, HasDirDerivAtE (valueFn f g) x u dV ∧
        IsGreatest (lagVals f g x u y) dV ∧
        ∀ v : E m, criticalConeVP F f g G x y dV (WithLp.toLp 2 (u, v)) →
          IsDirQNVP f g G x y u v (Wset f g x y u v) →
          ∃ (lV : ℝ) (lg : E p) (lG : E q) (l : E p),
            gradX F (WithLp.toLp 2 (x, y))
                - lV • ∑ i, l i • gradX (fun z => g z i) (WithLp.toLp 2 (x, y))
                + ∑ i, lg i • gradX (fun z => g z i) (WithLp.toLp 2 (x, y))
                + ∑ j, lG j • gradX (fun z => G z j) (WithLp.toLp 2 (x, y)) = 0 ∧
            gradY F (WithLp.toLp 2 (x, y)) + lV • gradY f (WithLp.toLp 2 (x, y))
                + ∑ i, lg i • gradY (fun z => g z i) (WithLp.toLp 2 (x, y))
                + ∑ j, lG j • gradY (fun z => G z j) (WithLp.toLp 2 (x, y)) = 0 ∧
            0 ≤ lV ∧
            (∀ i, 0 ≤ lg i) ∧ ∑ i, lg i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
            ∑ i, lg i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y))
              (WithLp.toLp 2 (u, v)) = 0 ∧
            (∀ j, 0 ≤ lG j) ∧ ∑ j, lG j * G (WithLp.toLp 2 (x, y)) j = 0 ∧
            ∑ j, lG j * fderiv ℝ (fun z => G z j) (WithLp.toLp 2 (x, y))
              (WithLp.toLp 2 (u, v)) = 0 ∧
            gradY f (WithLp.toLp 2 (x, y))
                + ∑ i, l i • gradY (fun z => g z i) (WithLp.toLp 2 (x, y)) = 0 ∧
            (∀ i, 0 ≤ l i) ∧ ∑ i, l i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
            ∑ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y))
              (WithLp.toLp 2 (u, v)) = 0 := by sorry

end DirKKTBilevel.VP.Supplement
