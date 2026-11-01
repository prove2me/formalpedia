-- Prove2me | Theorems.Thm_CongestionTaxes_lemma_1
-- name    : CongestionTaxes.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:28.654831+00:00
-- url     : https://prove2.me/theorems/947da282-89fa-49d6-a427-499f853ef262
-- title:
--   Lemma 1 — taxes are nonnegative, modified costs non-decreasing, and the recursion (c)
-- statement:
--   Let $\ell$ satisfy Assumption 1 with $\ell(0)=0$, and let the series $\sum_{i\ge0}i\ell(i)v^i/i!$ of (10) converge for every $v\ge0$, and let $f$, $\tau$ be the modified cost and the tax of Definition 4. For all $v\in\mathbb R_{\ge0}$ and $x\in\mathbb N_0$:
--
--   1. (a) $\tau(x,v)\ge0$;
--   2. (b) $f(x+1,v)\ge f(x,v)$;
--   3. (c) $x\ell(x)-xf(x,v)+vf(x+1,v)=p(v)$.
--
--   These three properties drive the proof of Theorem 3: (a) makes the mechanism a taxation, (b) and (c) give the fractional smoothness inequality (13).
--
--   Differences from the source:
--
--   - encoding: $p:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ of (10), a real number for every $v\ge0$ → the hypothesis that the series (10) converges for every $v\ge0$; reason: it excludes only the costs for which $p$ is undefined (e.g. $\ell(x)=e^{x^2}$); the Lean `tsum` of a divergent series is $0$. It is implied by $\rho_\ell<\infty$ (Lemma 4, p.28) and strictly weaker ($\ell(x)=e^x$ has a convergent series and $\rho_\ell=\infty$)
--   - encoding: $\ell:\mathbb N\to\mathbb R_{>0}$ extended by $\ell(0)=0$ → $\ell:\mathbb N\to\mathbb R$ with $\ell(0)=0$ inside Assumption 1, $\rho_\ell$ in $[0,\infty]$; reason: the paper's own extension (p.5); same instances
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Lemma 1, p.18; proof in A.2.2, pp.28–30

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_modifiedCost
import Definitions.Def_CongestionTaxes_tax

open scoped ENNReal

namespace CongestionTaxes

/-- **Lemma 1** (Paccagnan, Gairing, arXiv:2105.07480v2, Lemma 1, p.18). For every resource cost
`ℓ` satisfying Assumption 1 whose series (10) converges, and all `v ∈ ℝ≥0`, `x ∈ ℕ₀`, the taxation mechanism of
Definition 4 satisfies:
1. (a) `τ(x, v) ≥ 0`;
2. (b) `f(x + 1, v) ≥ f(x, v)`;
3. (c) `x ℓ(x) − x f(x, v) + v f(x + 1, v) = p(v)`.

**Formalization Note** The series (10) is assumed to converge for every `v ≥ 0`, so that
`p : ℝ≥0 → ℝ≥0` is defined as on p.18 and the Lean `tsum` is its value (a divergent `tsum` is the junk
value `0`). This excludes only the cost functions for which `p` is undefined; it is implied by
`ρ_ℓ < ∞` (proof of Lemma 4, p.28) but strictly weaker (`ℓ(x) = eˣ` has convergent series and
`ρ_ℓ = ∞`). The page states no condition on `ρ_ℓ`. -/
theorem lemma_1 (ℓ : ℕ → ℝ) (hℓ : Assumption1 ℓ) (hsum : ∀ v : ℝ, 0 ≤ v →
      Summable (fun i : ℕ => (i : ℝ) * ℓ i * v ^ i / (i.factorial : ℝ))) (v : ℝ) (hv : 0 ≤ v)
    (x : ℕ) :
    0 ≤ tax ℓ x v ∧ modifiedCost ℓ x v ≤ modifiedCost ℓ (x + 1) v ∧
      (x : ℝ) * ℓ x - (x : ℝ) * modifiedCost ℓ x v + v * modifiedCost ℓ (x + 1) v =
        poissonValue ℓ v := by sorry

end CongestionTaxes
