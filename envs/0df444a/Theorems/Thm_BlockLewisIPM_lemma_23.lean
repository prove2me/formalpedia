-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_23
-- name    : BlockLewisIPM.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:13.327201+00:00
-- url     : https://prove2.me/theorems/34af83a3-f361-4fc4-8db6-908549b059e8
-- title:
--   Lemma 23 — the smoothed preconditioner is well defined, close and second-order smooth
-- statement:
--   Let $\phi$ be a $1$-self-concordant barrier on a compact convex $K\subset\mathbb R^k$, let $x\in\operatorname{int}K$, $M=\nabla^2\phi(x)$, $S=(\nabla^2\phi)^{-1}$ and $C_\phi=(\nabla^2\phi)^{-1/2}$, and let $\sigma,r_{\max}<1/4$ with $\sigma>0$. For every $y$ with $r=\|x-y\|_M\le r_{\max}$, the smoothed $\widetilde C(y,M)$ is well defined and differentiable at $y$, and
--
--   1. $\widetilde S(x,M)\approx_{4\sigma}S(x)$ and $\widetilde C(x,M)\approx_{2\sigma}C_\phi(x)$;
--   2. $\widetilde S(y,M)\approx_{4r_{\max}}\widetilde S(x,M)$ and $\widetilde C(y,M)\approx_{2r_{\max}}\widetilde C(x,M)$;
--   3. $\|\operatorname{sym}(\widetilde C(y,M)^{-1}D\widetilde C(y,M)[h])\|_{\mathrm{op}}\le(1+2(r_{\max}+\sigma))\|h\|_M$;
--   4. $\|\operatorname{sym}(\widetilde C(x,M)^{-1}(\widetilde C(y,M)-\widetilde C(x,M)))\|_{\mathrm{op}}\le4r+16kr^2$;
--   5. $\|\operatorname{sym}((\widetilde C(y,M)-\widetilde C(x,M)-D\widetilde C(x,M)[y-x])\widetilde C(x,M)^{-1})\|_{\mathrm{op}}\le(8k+20\sqrt k/\sigma)r^2$.
--
--   This replaces higher-order self-concordance: the smoothing gives the second-order control the Lewis weight analysis needs.
--
--   Differences from the source:
--   - reading: ϕ a 1-self-concordant function on K → ϕ a 1-self-concordant barrier on a compact convex K, x ∈ int K; reason: the proof uses "Point 1 in Lemma 3"; compactness is the blocks' standing assumption (§2.1) and makes the Hessian positive definite
--   - reading: "well defined" → the smoothing ball lies in int K, the expectation is integrable, S̃(y, M) is positive definite, and y ↦ C̃(y, M) is differentiable at y; reason: items 3 and 5 use D
--   - encoding: dimension d → dimension k; reason: name only
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 23, p.18

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 23**, p.18. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization
over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** The page's dimension `d` is `k` here. `ϕ` is a `1`-self-concordant barrier (the
proof uses "Point 1 in Lemma 3", reading R6) on a compact convex `K`, the blocks' standing assumption
(§2.1, p.3), so its Hessian is positive definite. "Well defined" is read as: the smoothing ball stays in
`int K`, the expectation exists, `S̃(y, M)` is positive definite, and `y ↦ C̃(y, M)` is differentiable at
`y`, since items 3 and 5 use `D`. Items 4 and 5 keep the page's different orders of factors. -/
theorem lemma_23 {k : ℕ} (K : Set (Eu k)) (φ : Eu k → ℝ) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hφ : EntropicBarrier.Universal.IsNuSelfConcordantBarrier K φ 1)
    (x : Fin k → ℝ) (hx : WithLp.toLp 2 x ∈ interior K) (σ rmax : ℝ) (hσ : 0 < σ) (hσ' : σ < 1 / 4)
    (hr : rmax < 1 / 4) :
    let M := hessMat φ x
    let S : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ := fun y => (hessMat φ y)⁻¹
    let Cm : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ := fun y => matInvSqrt (hessMat φ y)
    let St := smoothedS φ σ M
    let Ct := smoothedC φ σ M
    ApproxEq (4 * σ) (St x) (S x) ∧ ApproxEq (2 * σ) (Ct x) (Cm x) ∧
    ∀ y : Fin k → ℝ, wNorm M (x - y) ≤ rmax →
      let r := wNorm M (x - y)
      ((∀ u ∈ Metric.closedBall (0 : Eu k) 1,
          WithLp.toLp 2 (y + σ • (matInvSqrt M *ᵥ (u : Fin k → ℝ))) ∈ interior K) ∧
        (∀ a b, Integrable
          (fun u : Eu k => (S (y + σ • (matInvSqrt M *ᵥ (u : Fin k → ℝ)))) a b)
          (RegretBandits.Nonlinear.uniformBall k)) ∧
        (St y).PosDef ∧
        DifferentiableAt ℝ (fun y' : Eu k => (Ct y' : Fin k → Fin k → ℝ)) (WithLp.toLp 2 y)) ∧
      ApproxEq (4 * rmax) (St y) (St x) ∧ ApproxEq (2 * rmax) (Ct y) (Ct x) ∧
      (∀ h : Fin k → ℝ, opNorm (sym ((Ct y)⁻¹ * dSmoothedC φ σ M y h)) ≤
        (1 + 2 * (rmax + σ)) * wNorm M h) ∧
      opNorm (sym ((Ct x)⁻¹ * (Ct y - Ct x))) ≤ 4 * r + 16 * k * r ^ 2 ∧
      opNorm (sym ((Ct y - Ct x - dSmoothedC φ σ M x (y - x)) * (Ct x)⁻¹)) ≤
        (8 * k + 20 * Real.sqrt k / σ) * r ^ 2 := by sorry

end BlockLewisIPM
