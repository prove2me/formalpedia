-- Prove2me | Theorems.Thm_CongestionTaxes_lemma_1_a_ratio
-- name    : CongestionTaxes.lemma_1_a_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:45.805544+00:00
-- url     : https://prove2.me/theorems/0708df86-8e0a-4a4f-9e13-845a56396b55
-- title:
--   Proof of Lemma 1(a), p.28 — $p(v)$ dominates the ratio of partial sums
-- statement:
--   Let $\ell$ satisfy Assumption 1 with $\ell(0)=0$, and let the series $\sum_{i\ge0}i\ell(i)v^i/i!$ of (10) converge for every $v\ge0$, and let $c(i)=i\ell(i)$. Then for all $x\in\mathbb N$ and $v>0$,
--
--   $$
--   p(v)\ \ge\ \frac{\sum_{i=0}^{x}c(i)\,v^i/i!}{\sum_{j=0}^{x-1}v^j/j!}.
--   $$
--
--   This inequality is equivalent to $f(x,v)\ge\ell(x)$, i.e. to the nonnegativity of the taxes of Definition 4.
--
--   Differences from the source:
--
--   - encoding: $p:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ of (10), a real number for every $v\ge0$ → the hypothesis that the series (10) converges for every $v\ge0$; reason: it excludes only the costs for which $p$ is undefined (e.g. $\ell(x)=e^{x^2}$); the Lean `tsum` of a divergent series is $0$. It is implied by $\rho_\ell<\infty$ (Lemma 4, p.28) and strictly weaker ($\ell(x)=e^x$ has a convergent series and $\rho_\ell=\infty$)
--   - encoding: $\ell:\mathbb N\to\mathbb R_{>0}$ extended by $\ell(0)=0$ → $\ell:\mathbb N\to\mathbb R$ with $\ell(0)=0$ inside Assumption 1, $\rho_\ell$ in $[0,\infty]$; reason: the paper's own extension (p.5); same instances
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, proof of Lemma 1(a), A.2.2, p.28

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_poissonValue

open scoped ENNReal

namespace CongestionTaxes

/-- Proof of Lemma 1(a) (Paccagnan, Gairing, arXiv:2105.07480v2, A.2.2, p.28): with
`c(i) = i ℓ(i)`, for all `x ∈ ℕ` and `v > 0`,
`p(v) ≥ (∑_{i=0}^x c(i) vⁱ / i!) / (∑_{j=0}^{x−1} vʲ / j!)`.

**Formalization Note** The series (10) is assumed to converge for every `v ≥ 0`, so that
`p : ℝ≥0 → ℝ≥0` is defined as on p.18 and the Lean `tsum` is its value (a divergent `tsum` is the junk
value `0`). This excludes only the cost functions for which `p` is undefined; it is implied by
`ρ_ℓ < ∞` (proof of Lemma 4, p.28) but strictly weaker (`ℓ(x) = eˣ` has convergent series and
`ρ_ℓ = ∞`). The page states no condition on `ρ_ℓ`. `∑_{j=0}^{x−1}` is `Finset.range x`. -/
theorem lemma_1_a_ratio (ℓ : ℕ → ℝ) (hℓ : Assumption1 ℓ) (hsum : ∀ v : ℝ, 0 ≤ v →
      Summable (fun i : ℕ => (i : ℝ) * ℓ i * v ^ i / (i.factorial : ℝ))) (x : ℕ) (hx : 1 ≤ x)
    (v : ℝ) (hv : 0 < v) :
    (∑ i ∈ Finset.range (x + 1), (i : ℝ) * ℓ i * v ^ i / (i.factorial : ℝ)) /
        (∑ j ∈ Finset.range x, v ^ j / (j.factorial : ℝ)) ≤ poissonValue ℓ v := by sorry

end CongestionTaxes
