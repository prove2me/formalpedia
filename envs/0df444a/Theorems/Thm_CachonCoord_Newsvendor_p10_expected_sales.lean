-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_p10_expected_sales
-- name    : CachonCoord.Newsvendor.p10_expected_sales
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:22.468175+00:00
-- url     : https://prove2.me/theorems/66ec352a-437a-4721-bc58-8b1b2837dd4c
-- title:
--   §6.2.1, p. 10 — expected sales S(q) = q − ∫₀^q F, leftover inventory I(q) = q − S(q), lost sales L(q) = μ − S(q)
-- statement:
--   Let $D \ge 0$ be the demand with distribution function $F$ and finite mean $\mu = E[D]$. Expected sales $S(q) = E[\min(q, D)]$, expected leftover inventory $I(q) = E[(q-D)^+]$ and expected lost sales $L(q) = E[(D-q)^+]$ satisfy, for every order quantity $q$,
--   $$S(q) = q - \int_0^q F(y)\,dy, \qquad I(q) = q - S(q), \qquad L(q) = \mu - S(q).$$
--
--   These identities are the basis of every profit function in Cachon's chapter: they turn the retailer's and supplier's expected profits into functions of $S(q)$ alone.
--
--   **Formalization Note** The local `expSales`, `expLeftover`, and `meanDemand` are Bochner expectations. The probability measure is supported on $[0,\infty)$ and has integrable demand, so the expectations are well defined. The chapter’s continuous, strictly increasing, differentiable cdf assumptions are included; the identities also hold for negative $q$. The intermediate density integral from the page is omitted.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.1, p. 10 (displays for S(q), I(q), L(q))

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), 3rd draft, §6.2.1, p. 10: for a demand law on `[0, ∞)` with finite mean,
expected sales `S(q) = E[min(q, D)] = q − ∫_0^q F(y) dy`, expected leftover inventory
`I(q) = E[(q − D)⁺] = q − S(q)` and expected lost sales `L(q) = E[(D − q)⁺] = μ − S(q)`. -/
theorem p10_expected_sales (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x) (q : ℝ) :
    expSales D q = q - ∫ y in (0 : ℝ)..q, cdf D y ∧
      expLeftover D q = q - expSales D q ∧
      ∫ d, max (d - q) 0 ∂D = meanDemand D - expSales D q := by sorry

end CachonCoord.Newsvendor
