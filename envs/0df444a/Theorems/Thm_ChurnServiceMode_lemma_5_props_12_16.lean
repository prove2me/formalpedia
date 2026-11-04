-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_5_props_12_16
-- name    : ChurnServiceMode.lemma_5_props_12_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:46.560137+00:00
-- url     : https://prove2.me/theorems/d957b6d8-18dd-4ba2-85b0-06c4e4afb6b1
-- title:
--   Lemma 5, properties 12–16: the erf inequalities of the verification step
-- statement:
--   For real numbers $q,a,\theta,x$ (free variables) and $P(x)=3x-a-2ax^2+2x^3$:
--   1. (Property 12) if $q>0$ and $\theta<q$: $\theta(1+2q^2)-e^{q^2-\theta^2}q(1+2q^2)+2e^{q^2}q(1+q^2)\theta\sqrt\pi\bigl(\operatorname{erf}(q)-\operatorname{erf}(\theta)\bigr)\le0$;
--   2. (Property 13) if $a>0$ and $x\in(a-\frac1a,a)$: $2-2ax+2x^2+P(x)e^{x^2}\sqrt\pi\operatorname{erf}(x)>0$;
--   3. (Property 14) if $a>0$ and $x\in(a-\frac1a,a)$: $2-2ax+2x^2-P(x)e^{x^2}\sqrt\pi\operatorname{erfc}(x)>0$;
--   4. (Property 15) if $a>0$ and $x\in(a-\frac1a,a)$: $2-2ax+2x^2+P(x)e^{x^2}\sqrt\pi\bigl(1+\operatorname{erf}(x)\bigr)>0$;
--   5. (Property 16) if $a>0$, $\theta\in(a-\frac1a,a)$ and $x\in(\theta,a]$:
--   $$2(a-x)(a-3\theta+2a\theta^2-2\theta^3)-2e^{x^2-\theta^2}(1-a\theta+\theta^2)(1-2ax+2x^2)+e^{x^2}\sqrt\pi(a-3\theta+2a\theta^2-2\theta^3)(1-2ax+2x^2)\bigl(\operatorname{erf}(\theta)-\operatorname{erf}(x)\bigr)\le-2+2a^2-2a\theta.$$
--
--   They are used to verify the HJB inequality (14) for the candidate value function in Proposition 3.
--
--   Differences from the source: none.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 5, properties 12–16, pp.18–19 (PDF pp.18–19); proofs OA A, PDF pp.36–40

import Mathlib
import Definitions.Def_ChurnServiceMode_Params

open PSOutsourcing.PartialObs (erf)

namespace ChurnServiceMode

/-- **Lemma 5, properties 12–16** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), pp.18–19), with `erfc = 1 − erf` and free real
variables `q, a, θ, x` (not the model's threshold). Write `P(x) = 3x − a − 2ax² + 2x³`.
12. if `q > 0`, `θ < q`:
    `θ(1 + 2q²) − e^{q²−θ²} q(1 + 2q²) + 2e^{q²} q(1 + q²) θ √π (erf(q) − erf(θ)) ≤ 0`;
13. if `a > 0`, `x ∈ (a − 1/a, a)`: `2 − 2ax + 2x² + P(x) e^{x²} √π erf(x) > 0`;
14. if `a > 0`, `x ∈ (a − 1/a, a)`: `2 − 2ax + 2x² − P(x) e^{x²} √π erfc(x) > 0`;
15. if `a > 0`, `x ∈ (a − 1/a, a)`: `2 − 2ax + 2x² + P(x) e^{x²} √π (1 + erf(x)) > 0`;
16. if `a > 0`, `θ ∈ (a − 1/a, a)`, `x ∈ (θ, a]`:
    `2(a − x)(a − 3θ + 2aθ² − 2θ³) − 2e^{x²−θ²}(1 − aθ + θ²)(1 − 2ax + 2x²)
     + e^{x²}√π(a − 3θ + 2aθ² − 2θ³)(1 − 2ax + 2x²)(erf(θ) − erf(x)) ≤ −2 + 2a² − 2aθ`. -/
theorem lemma_5_props_12_16 :
    (∀ q θ : ℝ, 0 < q → θ < q →
      θ * (1 + 2 * q ^ 2) - Real.exp (q ^ 2 - θ ^ 2) * q * (1 + 2 * q ^ 2)
        + 2 * Real.exp (q ^ 2) * q * (1 + q ^ 2) * θ * Real.sqrt Real.pi * (erf q - erf θ) ≤ 0) ∧
    (∀ a x : ℝ, 0 < a → x ∈ Set.Ioo (a - 1 / a) a →
      0 < 2 - 2 * a * x + 2 * x ^ 2
        + (3 * x - a - 2 * a * x ^ 2 + 2 * x ^ 3) * Real.exp (x ^ 2) * Real.sqrt Real.pi * erf x) ∧
    (∀ a x : ℝ, 0 < a → x ∈ Set.Ioo (a - 1 / a) a →
      0 < 2 - 2 * a * x + 2 * x ^ 2
        - (3 * x - a - 2 * a * x ^ 2 + 2 * x ^ 3) * Real.exp (x ^ 2) * Real.sqrt Real.pi * erfc x) ∧
    (∀ a x : ℝ, 0 < a → x ∈ Set.Ioo (a - 1 / a) a →
      0 < 2 - 2 * a * x + 2 * x ^ 2
        + (3 * x - a - 2 * a * x ^ 2 + 2 * x ^ 3) * Real.exp (x ^ 2) * Real.sqrt Real.pi
          * (1 + erf x)) ∧
    (∀ a θ x : ℝ, 0 < a → θ ∈ Set.Ioo (a - 1 / a) a → x ∈ Set.Ioc θ a →
      2 * (a - x) * (a - 3 * θ + 2 * a * θ ^ 2 - 2 * θ ^ 3)
        - 2 * Real.exp (x ^ 2 - θ ^ 2) * (1 - a * θ + θ ^ 2) * (1 - 2 * a * x + 2 * x ^ 2)
        + Real.exp (x ^ 2) * Real.sqrt Real.pi * (a - 3 * θ + 2 * a * θ ^ 2 - 2 * θ ^ 3)
          * (1 - 2 * a * x + 2 * x ^ 2) * (erf θ - erf x)
        ≤ -2 + 2 * a ^ 2 - 2 * a * θ) := by sorry

end ChurnServiceMode
