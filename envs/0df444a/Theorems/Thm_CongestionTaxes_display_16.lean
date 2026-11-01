-- Prove2me | Theorems.Thm_CongestionTaxes_display_16
-- name    : CongestionTaxes.display_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:00.773737+00:00
-- url     : https://prove2.me/theorems/27457f3a-b76a-470e-8d0f-834ebe713a56
-- title:
--   Display (16), p.29 — $p(v)\ge g(x,v)$
-- statement:
--   Let $\ell$ satisfy Assumption 1 with $\ell(0)=0$, and let the series $\sum_{i\ge0}i\ell(i)v^i/i!$ of (10) converge for every $v\ge0$, and let $c(i)=i\ell(i)$. Then for all $x\in\mathbb N$ and $v>0$,
--
--   $$
--   p(v)\ \ge\ \frac{\sum_{i=1}^{x}\frac{x\,c(i)-i\,c(i-1)}{i!}v^i}{\sum_{i=0}^{x}\frac{x-i}{i!}v^i}=g(x,v).
--   $$
--
--   This inequality is equivalent to $f(x+1,v)\ge f(x,v)$, the monotonicity of the modified costs (Lemma 1(b)).
--
--   Differences from the source:
--
--   - encoding: $p:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ of (10), a real number for every $v\ge0$ → the hypothesis that the series (10) converges for every $v\ge0$; reason: it excludes only the costs for which $p$ is undefined (e.g. $\ell(x)=e^{x^2}$); the Lean `tsum` of a divergent series is $0$. It is implied by $\rho_\ell<\infty$ (Lemma 4, p.28) and strictly weaker ($\ell(x)=e^x$ has a convergent series and $\rho_\ell=\infty$)
--   - encoding: $\ell:\mathbb N\to\mathbb R_{>0}$ extended by $\ell(0)=0$ → $\ell:\mathbb N\to\mathbb R$ with $\ell(0)=0$ inside Assumption 1, $\rho_\ell$ in $[0,\infty]$; reason: the paper's own extension (p.5); same instances
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (16), proof of Lemma 1(b), A.2.2, p.29

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_gRatio

open scoped ENNReal

namespace CongestionTaxes

/-- Display (16) (Paccagnan, Gairing, arXiv:2105.07480v2, proof of Lemma 1(b), p.29): with
`c(i) = i ℓ(i)`, for all `x ∈ ℕ` and `v > 0`,
`p(v) ≥ (∑_{i=1}^x ((x c(i) − i c(i−1)) / i!) vⁱ) / (∑_{i=0}^x ((x − i) / i!) vⁱ) = g(x, v)`.

**Formalization Note** The series (10) is assumed to converge for every `v ≥ 0`, so that
`p : ℝ≥0 → ℝ≥0` is defined as on p.18 and the Lean `tsum` is its value (a divergent `tsum` is the junk
value `0`). This excludes only the cost functions for which `p` is undefined; it is implied by
`ρ_ℓ < ∞` (proof of Lemma 4, p.28) but strictly weaker (`ℓ(x) = eˣ` has convergent series and
`ρ_ℓ = ∞`). The page states no condition on `ρ_ℓ`. -/
theorem display_16 (ℓ : ℕ → ℝ) (hℓ : Assumption1 ℓ) (hsum : ∀ v : ℝ, 0 ≤ v →
      Summable (fun i : ℕ => (i : ℝ) * ℓ i * v ^ i / (i.factorial : ℝ))) (x : ℕ) (hx : 1 ≤ x)
    (v : ℝ) (hv : 0 < v) :
    gRatio (fun i => (i : ℝ) * ℓ i) x v ≤ poissonValue ℓ v := by sorry

end CongestionTaxes
