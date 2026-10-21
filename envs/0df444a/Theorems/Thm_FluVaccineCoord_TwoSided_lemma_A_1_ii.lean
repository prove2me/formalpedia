-- Prove2me | Theorems.Thm_FluVaccineCoord_TwoSided_lemma_A_1_ii
-- name    : FluVaccineCoord.TwoSided.lemma_A_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:36.579456+00:00
-- url     : https://prove2.me/theorems/be8d4bc7-fe18-42ac-b964-807a57fe40ee
-- title:
--   Lemma A.1(ii), Online Supplement p. 1, corrected — the marginal social benefit B is strictly decreasing above x_zr and changes sign at xᶜ₁
-- statement:
--   Let $B$ be the marginal social benefit (6) of not vaccinating the individual with infection cost $\hat x$, let $x_{zr} = \bar x(1-h_{zr})$ be the threshold of the zero-risk vaccination fraction (5), and assume, in addition to the standing assumptions, that $(1-h)u(h) + hv(h)$ is **strictly** convex on $[0, h_{zr}]$. Then:
--
--   1. $B$ is strictly decreasing on $(x_{zr}, \bar x]$;
--   2. a threshold $x^c_1$ satisfying (8) exists;
--   3. every $x^c_1$ satisfying (8) lies in $[x_{zr}, \bar x)$, and for $0 < x \le \bar x$,
--   $$B(x) > 0 \ \text{ if } x < x^c_1, \qquad B(x) < 0 \ \text{ if } x > x^c_1.$$
--
--   So $W(\cdot, Q_r)$ increases up to $x^c_1$ and decreases after it on the region where demand does not exceed supply; this is the step behind Proposition 1.
--
--   **Formalization Note** This is a corrected statement. With Assumption 1(iii) as printed (convexity only), $(1-h)u + hv$ and $h(1-h)(u-v)$ can both be affine on an interval, and then $B$ is constant there; strict convexity is the added hypothesis. The page cites "(12)" for $x^c_1$, where (8) is meant. Monotonicity is stated on $(x_{zr},\bar x]$ and the sign claims on $(0,\bar x]$, where $B$ does not depend on the value of the derivative at the kink $h_{zr}$ or at $h = 1$.
-- source:
--   Arifoğlu & Tang, A Two-Sided Incentive Program for Coordinating the Influenza Vaccine Supply Chain, revised manuscript of 17 June 2020 (MSOM 2022, doi:10.1287/msom.2020.0938), Online Supplement p. 1, Lemma A.1(ii) (corrected: Assumption 1(iii) strict; '(12)' read as (8))

import Mathlib
import Definitions.Def_FluVaccineCoord_TwoSided_Model

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set

/-- Lemma A.1(ii), Online Supplement p. 1, **corrected**: under the standing assumptions and
Assumption 1(iii) read strictly (strict convexity of `(1 − h)u(h) + hv(h)` on `[0, h_zr]`), the
marginal social benefit `B` of (6) is strictly decreasing on `(x_zr, x̄]`, a threshold `xᶜ₁`
satisfying (8) exists, and for every such `xᶜ₁`: `xᶜ₁ ∈ [x_zr, x̄)`, `B(x) > 0` for `0 < x < xᶜ₁`,
and `B(x) < 0` for `xᶜ₁ < x ≤ x̄`. The page cites "(12)" where (8) is meant. Its "for `x ≥ x_zr`" is
stated on `(x_zr, x̄]` and its sign claims on `(0, x̄]`, where `B` does not depend on the derivative
conventions at the kink `h_zr` and at `h = 1`. -/
theorem lemma_A_1_ii (M : Model) (hS : Standing M)
    (hconv : StrictConvexOn ℝ (Icc 0 (hzr M)) (fun h => (1 - h) * M.u h + h * M.v h)) :
    StrictAntiOn (Bm M) (Ioc (xzr M) M.xbar) ∧ (∃ xc1, IsXc1 M xc1) ∧
      ∀ xc1, IsXc1 M xc1 → xc1 ∈ Ico (xzr M) M.xbar ∧
        (∀ x ∈ Ioc 0 M.xbar, x < xc1 → 0 < Bm M x) ∧
        (∀ x ∈ Ioc 0 M.xbar, xc1 < x → Bm M x < 0) := by sorry

end FluVaccineCoord.TwoSided
