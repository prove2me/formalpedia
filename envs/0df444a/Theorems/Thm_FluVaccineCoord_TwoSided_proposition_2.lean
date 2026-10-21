-- Prove2me | Theorems.Thm_FluVaccineCoord_TwoSided_proposition_2
-- name    : FluVaccineCoord.TwoSided.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:43.921869+00:00
-- url     : https://prove2.me/theorems/b9518c96-986d-4e97-a016-2a566953020c
-- title:
--   Proposition 2, p. 13 — the socially-optimal planned production Q⁽ᶜ⁾ exists, is positive and satisfies the first-order condition (10)
-- statement:
--   Fix $x^c_1$ satisfying (8). The planner's problem $\max_{Q \ge 0} W^{(c)}(Q)$ of (9) has a maximizer $Q^{(c)} > 0$. Every maximizer $Q^{(c)} \ge 0$ is positive, and if the yield distribution $F$ has a density, it satisfies
--   $$\int_0^{\bar G(x^c_1)/Q^{(c)}} \bar x\,\bigl[-B\bigl(x^c_2(yQ^{(c)})\bigr)\bigr]\, y\, dF(y) = c, \qquad (10)$$
--   where $B$ is the marginal social benefit (6) and $x^c_2(Q_r) = \bar G^{-1}(\min\{1, Q_r\}) = \bar x(1 - \min\{1,Q_r\})$ (11).
--
--   At the optimum, the expected marginal welfare of one more planned unit equals its cost $c$. The existence part makes the hypothesis "$Q^{(c)}$ is socially optimal" of Propositions 6 and 7 satisfiable.
--
--   **Formalization Note** The paper asserts (10) without stating that $F$ has a density; its proof differentiates through the density $f$ at $\bar G(x^c_1)/Q$, so the density is a disclosed hypothesis of the first-order condition only. Existence and positivity carry no extra hypothesis. The integral is over $y \in [0, \bar G(x^c_1)/Q^{(c)}]$ against the law of $Y$.
-- source:
--   Arifoğlu & Tang, A Two-Sided Incentive Program for Coordinating the Influenza Vaccine Supply Chain, revised manuscript of 17 June 2020 (MSOM 2022, doi:10.1287/msom.2020.0938), p. 13, Proposition 2, (10)–(11) (density of F: the proof's assumption, Online Supplement p. 3)

import Mathlib
import Definitions.Def_FluVaccineCoord_TwoSided_Model

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set

/-- Proposition 2, p. 13: the planner's problem (9) has a maximizer `Q⁽ᶜ⁾` over `Q ≥ 0`; every
maximizer is positive and, when the yield law has a density, satisfies the first-order condition
(10), `∫₀^{Ḡ(xᶜ₁)/Q⁽ᶜ⁾} x̄ [−B(xᶜ₂(y Q⁽ᶜ⁾))] y dF(y) = c`, with `xᶜ₂` of (11). The density is the
proof's own assumption (it differentiates through `f(Ḡ(xᶜ₁)/Q)`, Online Supplement p. 3). -/
theorem proposition_2 (M : Model) (hS : Standing M) (xc1 : ℝ) (hx : IsXc1 M xc1) :
    (∃ Qc, 0 < Qc ∧ IsMaxOn (Wc M xc1) (Ici 0) Qc) ∧
      ∀ Qc, 0 ≤ Qc → IsMaxOn (Wc M xc1) (Ici 0) Qc → 0 < Qc ∧
        (M.μ ≪ volume →
          ∫ y in Icc 0 (Gbar M xc1 / Qc), M.xbar * (-(Bm M (xc2 M (y * Qc)))) * y ∂M.μ
            = M.c) := by sorry

end FluVaccineCoord.TwoSided
