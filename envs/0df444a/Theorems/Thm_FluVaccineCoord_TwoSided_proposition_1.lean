-- Prove2me | Theorems.Thm_FluVaccineCoord_TwoSided_proposition_1
-- name    : FluVaccineCoord.TwoSided.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:36.610784+00:00
-- url     : https://prove2.me/theorems/f31c89e3-9460-47eb-917a-91099f441e9b
-- title:
--   Proposition 1, p. 12, corrected — x⁽ᶜ⁾(Qᵣ) with Ḡ(x⁽ᶜ⁾(Qᵣ)) = min{Ḡ(xᶜ₁), Qᵣ} maximizes ex-post welfare; unique for Qᵣ ≠ h_zr
-- statement:
--   Let $x^c_1$ satisfy (8) and let $Q_r > 0$ be the realized vaccine supply. Put $h^{(c)}(Q_r) = \min\{\bar G(x^c_1), Q_r\}$ and $x^{(c)}(Q_r) = \bar x(1 - h^{(c)}(Q_r))$, the threshold whose demand is $h^{(c)}(Q_r)$:
--   $$\bar G\bigl(x^{(c)}(Q_r)\bigr) = h^{(c)}(Q_r) = \min\{\bar G(x^c_1), Q_r\}. \qquad (7)$$
--   Then:
--
--   1. $x^{(c)}(Q_r) \in [x_{zr}, \bar x)$;
--   2. $x^{(c)}(Q_r)$ maximizes the ex-post welfare $W(\cdot, Q_r)$ of (4) over $[0,\bar x]$;
--   3. if $(1-h)u(h)+hv(h)$ is strictly convex on $[0,h_{zr}]$, every maximizer $\hat x \in [0, \bar x]$ yields the vaccinated fraction $h(\hat x, Q_r) = h^{(c)}(Q_r)$, and if moreover $Q_r \ne h_{zr}$, the maximizer is unique.
--
--   The social planner thus vaccinates $\bar G(x^c_1)$ individuals when supply is abundant and uses all the supply when it is scarce.
--
--   **Formalization Note** Corrected statement. The page asserts uniqueness for every $Q_r \ge 0$. At $Q_r = 0$ welfare does not depend on the threshold. At $Q_r = h_{zr}$ with $x^c_1 = x_{zr}$ every threshold in $[0,x_{zr}]$ is optimal, because $u = v = 0$ at $h_{zr}$. Both cases are excluded from the uniqueness claim, and the uniqueness claims carry the strict-convexity hypothesis of Lemma A.1(ii) (without it, $B$ can vanish on an interval and the maximizers form an interval). Existence and optimality hold under the standing assumptions.
-- source:
--   Arifoğlu & Tang, A Two-Sided Incentive Program for Coordinating the Influenza Vaccine Supply Chain, revised manuscript of 17 June 2020 (MSOM 2022, doi:10.1287/msom.2020.0938), p. 12, Proposition 1, (7)–(8) (corrected: Qᵣ > 0; uniqueness for Qᵣ ≠ h_zr under strictly convex Assumption 1(iii))

import Mathlib
import Definitions.Def_FluVaccineCoord_TwoSided_Model

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set

/-- Proposition 1, p. 12, **corrected**: for every realized supply `Qᵣ > 0` the threshold
`x⁽ᶜ⁾(Qᵣ) = x̄(1 − h⁽ᶜ⁾(Qᵣ))`, with `h⁽ᶜ⁾(Qᵣ) = min{Ḡ(xᶜ₁), Qᵣ}` (7), lies in `[x_zr, x̄)` and
maximizes the ex-post welfare `W(·, Qᵣ)` of (4) over `[0, x̄]`. Under Assumption 1(iii) read
strictly, every maximizer yields the vaccinated fraction `h⁽ᶜ⁾(Qᵣ)`, and for `Qᵣ ≠ h_zr` the
maximizer is unique. (The page claims uniqueness for all `Qᵣ ≥ 0`; it fails at `Qᵣ = 0`, and at
`Qᵣ = h_zr` when `xᶜ₁ = x_zr`, where every threshold in `[0, x_zr]` is optimal.) -/
theorem proposition_1 (M : Model) (hS : Standing M) (xc1 : ℝ) (hx : IsXc1 M xc1)
    (Qr : ℝ) (hQ : 0 < Qr) :
    xc M xc1 Qr ∈ Ico (xzr M) M.xbar ∧
      IsMaxOn (fun x => welfare M x Qr) (Icc 0 M.xbar) (xc M xc1 Qr) ∧
      (StrictConvexOn ℝ (Icc 0 (hzr M)) (fun h => (1 - h) * M.u h + h * M.v h) →
        (∀ x ∈ Icc 0 M.xbar, IsMaxOn (fun x => welfare M x Qr) (Icc 0 M.xbar) x →
          vacc M x Qr = hc M xc1 Qr) ∧
        (Qr ≠ hzr M → ∀ x ∈ Icc 0 M.xbar,
          IsMaxOn (fun x => welfare M x Qr) (Icc 0 M.xbar) x → x = xc M xc1 Qr)) := by sorry

end FluVaccineCoord.TwoSided
