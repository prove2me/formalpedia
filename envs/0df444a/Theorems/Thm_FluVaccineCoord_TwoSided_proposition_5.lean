-- Prove2me | Theorems.Thm_FluVaccineCoord_TwoSided_proposition_5
-- name    : FluVaccineCoord.TwoSided.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:44.787044+00:00
-- url     : https://prove2.me/theorems/b9728948-a435-45d0-9300-be2089670f89
-- title:
--   Proposition 5, p. 17 — the incentive program (18)–(19) coordinates demand and supply: x⁽ᴵ⁾ = x⁽ᶜ⁾ and Q⁽ᴵ⁾ = Q⁽ᶜ⁾
-- statement:
--   Fix $x^c_1$ satisfying (8) and a constant $K$, and let the planner offer the incentive program $I = (r(Q_r), T(Q_r))$ of (18)–(19). Then:
--
--   1. for every realized supply $Q_r \ge 0$, the individuals' equilibrium threshold under the incentive $r(Q_r)$ equals the socially-optimal one,
--   $$x^{(I)}(Q_r) = x^{(c)}(Q_r);$$
--   2. a planned quantity $Q \ge 0$ maximizes the manufacturer's expected profit $\pi^{(I)}$ of (17) over $Q \ge 0$ if and only if it maximizes the planner's objective $W^{(c)}$ of (9), i.e. $Q^{(I)} = Q^{(c)}$.
--
--   The incentive $r$ coordinates the demand side and the transfer $T$ the supply side.
--
--   **Formalization Note** The threshold $x^{(I)}(Q_r)$ is the least $x \in [0,\bar x]$ at which the marginal individual strictly gains from seeking vaccination ($\bar x$ if none), as in the proof of Proposition 5; it is computed from the primitives, not assumed. Part 2 is stated as equality of the sets of maximizers, so it does not presuppose that the maximizer is unique.
-- source:
--   Arifoğlu & Tang, A Two-Sided Incentive Program for Coordinating the Influenza Vaccine Supply Chain, revised manuscript of 17 June 2020 (MSOM 2022, doi:10.1287/msom.2020.0938), p. 17, Proposition 5; threshold rule: Online Supplement p. 6, proof of Proposition 5

import Mathlib
import Definitions.Def_FluVaccineCoord_TwoSided_Model

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set

/-- Proposition 5, p. 17: under the incentive program `(r(Qᵣ), T(Qᵣ))` of (18)–(19) with any
constant `K`, (i) the individuals' equilibrium threshold equals the socially-optimal one,
`x⁽ᴵ⁾(Qᵣ) = x⁽ᶜ⁾(Qᵣ)`, for every realized supply `Qᵣ ≥ 0`; (ii) the manufacturer's optimal
production quantities (maximizers of `π⁽ᴵ⁾` of (17) over `Q ≥ 0`) are exactly the planner's
(maximizers of `W⁽ᶜ⁾` of (9)), i.e. `Q⁽ᴵ⁾ = Q⁽ᶜ⁾`. -/
theorem proposition_5 (M : Model) (hS : Standing M) (xc1 : ℝ) (hx : IsXc1 M xc1) (K : ℝ) :
    (∀ Qr, 0 ≤ Qr → thr M (rInc M xc1 Qr) Qr = xc M xc1 Qr) ∧
      ∀ Q, 0 ≤ Q →
        (IsMaxOn (piI M xc1 K) (Ici 0) Q ↔ IsMaxOn (Wc M xc1) (Ici 0) Q) := by sorry

end FluVaccineCoord.TwoSided
