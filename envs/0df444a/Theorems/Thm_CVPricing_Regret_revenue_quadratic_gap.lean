-- Prove2me | Theorems.Thm_CVPricing_Regret_revenue_quadratic_gap
-- name    : CVPricing.Regret.revenue_quadratic_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:14:46.307463+00:00
-- url     : https://prove2.me/theorems/60cca5fe-9f2d-4eb2-bb07-11677516e6dc
-- title:
--   Eq. (17) — |r(p) − r(p_opt)| ≤ (K/2)(p − p_opt)² with K = sup |r''|
-- statement:
--   Write $r(p) = r(p, a^{(0)})$ and let
--
--   $$K := \sup_{p \in [p_l, p_h]} |r''(p)|.$$
--
--   Then for every price $p \in [p_l, p_h]$,
--
--   $$|r(p) - r(p_{\mathrm{opt}})| \le \frac K2 (p - p_{\mathrm{opt}})^2. \tag{17}$$
--
--   Because $p_{\mathrm{opt}}$ is an interior maximizer, the revenue loss of a price is quadratic in its distance to the optimum; this turns the regret into a sum of squared pricing errors.
--
--   **Formalization Note** The paper writes $p \in \mathscr P$ without defining $\mathscr P$; it is the price interval $[p_l, p_h]$. $r''$ is the second derivative of $p \mapsto p\,h(a_0^{(0)} + a_1^{(0)}p)$; it is continuous on $[p_l, p_h]$, so $K$ is finite.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 782 (PDF 14), proof of Theorem 1, eq. (17)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP

namespace CVPricing.Regret

/-- Eq. (17) (den Boer–Zwart 2014, proof of Theorem 1, p. 782): with
`K := sup_{p ∈ [pl, ph]} |r''(p)|` (second derivative of `r(·) = r(·, a⁽⁰⁾)`),
`|r(p) − r(p_opt)| ≤ (K/2)(p − p_opt)²` for every `p ∈ [pl, ph]`. -/
theorem revenue_quadratic_gap (M : Model) :
    ∀ q ∈ Set.Icc M.pl M.ph,
      |revenue M.h M.a0 q - revenue M.h M.a0 (pOpt M)| ≤
        sSup ((fun x => |deriv (deriv (revenue M.h M.a0)) x|) '' Set.Icc M.pl M.ph) / 2 *
          (q - pOpt M) ^ 2 := by sorry

end CVPricing.Regret
