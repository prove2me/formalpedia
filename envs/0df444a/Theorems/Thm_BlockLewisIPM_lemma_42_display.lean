-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_42_display
-- name    : BlockLewisIPM.lemma_42_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:21.212504+00:00
-- url     : https://prove2.me/theorems/79fc4100-b196-446b-9595-5824b4090df2
-- title:
--   The concentration display in the proof of Lemma 42 — finite-sum smoothing
-- statement:
--   Let $\phi$ be a $1$-self-concordant barrier on a compact convex $K\subset\mathbb R^k$, $1\le k\le n_{\max}$, $x\in\operatorname{int}K$, $M=\nabla^2\phi(x)$, $0<\sigma\le1/10$, $\epsilon>0$ and $0<\delta\le1/2$. Let $K_s=1+\lceil1000\sigma^2\epsilon^{-2}\log(n_{\max}/\delta)\rceil$, let $u^{(1)},\dots,u^{(K_s)}$ be i.i.d. uniform on the unit ball, and let
--
--   $$\widehat S=\frac1{K_s}\sum_j\nabla^2\phi\bigl(x+\sigma M^{-1/2}u^{(j)}\bigr)^{-1},\qquad\widetilde S=\widetilde S(x,M).$$
--
--   Then
--
--   $$\Pr\bigl[\|\widetilde S^{-1/2}(\widehat S-\widetilde S)\widetilde S^{-1/2}\|_{\mathrm{op}}\ge\epsilon\bigr]\le\delta.$$
--
--   So the expectation defining the smoothed preconditioner can be replaced by a short finite sum.
--
--   Differences from the source:
--   - reading: K = 1 + 1000σ²ϵ⁻² log(n_max/δ), a real number → K_s = 1 + ⌈1000σ²ϵ⁻² log(n_max/δ)⌉; reason: a sample count is an integer
--   - reading: "our choice of σ" and "sufficiently small δ" (p.41) → σ ≤ 1/10 and δ ≤ 1/2; reason: the ranges the display needs
--   - reading: ϕ of Lemma 42 → a 1-self-concordant barrier on a compact convex K, x ∈ int K; reason: the blocks' standing assumption (§2.1)
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), the proof of Lemma 42, display on p.41; Algorithm 3, line 8, p.40

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **The concentration display in the proof of Lemma 42**, p.41, with `K` of Algorithm 3, p.40. Zhang,
Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain*
(manuscript, sha256 66072000…).

**Formalization Note.** `K_s` is the page's sample count `K`, with the printed real rounded up. The set is
`K`, `δ` is the failure probability of Algorithm 3, and `ϵ` is its accuracy. `σ ≤ 1/10` and `δ ≤ 1/2` are
"our choice of `σ`" and "sufficiently small `δ`", p.41. `M = ∇²ϕ(x)`. The samples are i.i.d. uniform on the
unit ball. Lemma 42's data structure and its time are not part of this display. -/
theorem lemma_42_display {k : ℕ} (K : Set (Eu k)) (φ : Eu k → ℝ) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hφ : EntropicBarrier.Universal.IsNuSelfConcordantBarrier K φ 1)
    (hk : 1 ≤ k) (nmax : ℕ) (hnmax : k ≤ nmax)
    (x : Fin k → ℝ) (hx : WithLp.toLp 2 x ∈ interior K) (σ ϵ δ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 10)
    (hϵ : 0 < ϵ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    let Ks : ℕ := 1 + ⌈1000 * σ ^ 2 * (ϵ ^ 2)⁻¹ * Real.log ((nmax : ℝ) / δ)⌉₊
    let M := hessMat φ x
    let St := smoothedS φ σ M x
    let Sh : (Fin Ks → Eu k) → Matrix (Fin k) (Fin k) ℝ := fun u =>
      (Ks : ℝ)⁻¹ • ∑ j, (hessMat φ (x + σ • (matInvSqrt M *ᵥ (u j : Fin k → ℝ))))⁻¹
    Measure.pi (fun _ : Fin Ks => RegretBandits.Nonlinear.uniformBall k)
        {u | ϵ ≤ opNorm (matInvSqrt St * (Sh u - St) * matInvSqrt St)} ≤
      ENNReal.ofReal δ := by sorry

end BlockLewisIPM
