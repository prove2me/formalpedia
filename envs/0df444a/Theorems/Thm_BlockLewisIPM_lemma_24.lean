-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_24
-- name    : BlockLewisIPM.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:17.542959+00:00
-- url     : https://prove2.me/theorems/c062af7f-efc1-4f55-adc0-d88d80683553
-- title:
--   Lemma 24 — the smoothed preconditioner under a change of reference metric
-- statement:
--   Let $\phi$ be a $1$-self-concordant barrier on a compact convex $K\subset\mathbb R^k$, let $x,x'\in\operatorname{int}K$, $M=\nabla^2\phi(x)$, $M'=\nabla^2\phi(x')$, and let $r=\|x-x'\|_M\le r_{\max}\le1/5$ and $0<\sigma<1/5$. Then
--
--   1. $\widetilde S(x,M)\approx_{4\sigma r}\widetilde S(x,M')$;
--   2. $\|\operatorname{sym}(\widetilde C(x,M)^{-1}(\widetilde C(x,M)-\widetilde C(x,M')))\|_{\mathrm{op}}\le2\sigma r+10k\sigma^2r^2$;
--   3. $\|\operatorname{sym}(\widetilde C(x,M')^{-1}(\widetilde C(x,M)-\widetilde C(x,M')))\|_{\mathrm{op}}\le2\sigma r+10k\sigma^2r^2$.
--
--   Changing the reference metric thus has an effect of order $\sigma r$, smaller by a factor $\sigma$ than moving the point.
--
--   Differences from the source:
--   - reading: K convex, x, x′ reference points → K compact convex, x, x′ ∈ int K; reason: the blocks' standing assumption (§2.1); the Hessians must be defined and positive definite
--   - encoding: dimension d → dimension k; reason: name only
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 24, p.21

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 24**, p.21. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization
over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** `K` is compact and convex, the blocks' standing assumption (§2.1, p.3), and
`x, x′ ∈ int K`. The page's dimension `d` is `k`. -/
theorem lemma_24 {k : ℕ} (K : Set (Eu k)) (φ : Eu k → ℝ) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hφ : EntropicBarrier.Universal.IsNuSelfConcordantBarrier K φ 1)
    (x x' : Fin k → ℝ) (hx : WithLp.toLp 2 x ∈ interior K) (hx' : WithLp.toLp 2 x' ∈ interior K)
    (σ rmax : ℝ) (hσ : 0 < σ) (hσ' : σ < 1 / 5) (hrmax : rmax ≤ 1 / 5)
    (hr : wNorm (hessMat φ x) (x - x') ≤ rmax) :
    let M := hessMat φ x
    let M' := hessMat φ x'
    let r := wNorm M (x - x')
    let D := smoothedC φ σ M x - smoothedC φ σ M' x
    ApproxEq (4 * σ * r) (smoothedS φ σ M x) (smoothedS φ σ M' x) ∧
    opNorm (sym ((smoothedC φ σ M x)⁻¹ * D)) ≤ 2 * σ * r + 10 * k * σ ^ 2 * r ^ 2 ∧
    opNorm (sym ((smoothedC φ σ M' x)⁻¹ * D)) ≤ 2 * σ * r + 10 * k * σ ^ 2 * r ^ 2 := by sorry

end BlockLewisIPM
