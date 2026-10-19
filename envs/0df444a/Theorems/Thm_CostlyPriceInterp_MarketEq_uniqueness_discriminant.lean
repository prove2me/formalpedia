-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_uniqueness_discriminant
-- name    : CostlyPriceInterp.MarketEq.uniqueness_discriminant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:36.531906+00:00
-- url     : https://prove2.me/theorems/2d08c328-0192-4da7-b450-c707faedc768
-- title:
--   Proof of Proposition 1, p. 56 — the discriminant of the cubic (18) is the printed Δ < 0, so f has one real root
-- statement:
--   Assume the standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$, and view (18) as the cubic $a\alpha^3 + b\alpha^2 + c\alpha + d$ with $a = \tau_e\tau_\varepsilon+\tau_\varepsilon\tau_\eta$, $b = 2\tau_e\tau_\varepsilon$, $c = \tau_e\tau_\varepsilon+\tau_e\tau_\eta+\tau_u\tau_\varepsilon$, $d = -\tau_e\tau_u$, whose evaluation is $f$. Its discriminant $\Delta = b^2c^2 - 4ac^3 - 4b^3d - 27a^2d^2 + 18abcd$ equals
--   $$\Delta = -\tau_\varepsilon\big(4\tau_e^3\tau_\eta^4 + 4\tau_e^4\tau_\eta^3 + 4\tau_e\tau_u^3\tau_\varepsilon^3 + 4\tau_e^3\tau_u\tau_\varepsilon^3 + 4\tau_e^4\tau_u\tau_\varepsilon^2 + 27\tau_e^4\tau_u^2\tau_\varepsilon + 12\tau_e^3\tau_\varepsilon\tau_\eta^3 + 4\tau_e^3\tau_\varepsilon^3\tau_\eta + 8\tau_e^4\tau_\varepsilon\tau_\eta^2 + 4\tau_e^4\tau_\varepsilon^2\tau_\eta + 4\tau_u^3\tau_\varepsilon^3\tau_\eta + 8\tau_e^2\tau_u^2\tau_\varepsilon^3 + 36\tau_e^3\tau_u^2\tau_\varepsilon^2 + 12\tau_e^3\tau_\varepsilon^2\tau_\eta^2 + 12\tau_e\tau_u^2\tau_\varepsilon^2\tau_\eta^2 + 24\tau_e^2\tau_u\tau_\varepsilon^2\tau_\eta^2 + 27\tau_e^2\tau_u^2\tau_\varepsilon\tau_\eta^2 + 48\tau_e^2\tau_u^2\tau_\varepsilon^2\tau_\eta + 36\tau_e^4\tau_u\tau_\varepsilon\tau_\eta + 12\tau_e\tau_u^2\tau_\varepsilon^3\tau_\eta + 12\tau_e^2\tau_u\tau_\varepsilon\tau_\eta^3 + 12\tau_e^2\tau_u\tau_\varepsilon^3\tau_\eta + 48\tau_e^3\tau_u\tau_\varepsilon\tau_\eta^2 + 52\tau_e^3\tau_u\tau_\varepsilon^2\tau_\eta + 54\tau_e^3\tau_u^2\tau_\varepsilon\tau_\eta\big),$$
--   which is negative; consequently $f$ has exactly one real root: any two real roots of $f$ coincide.
--
--   This is the uniqueness half of Proposition 1: since every linear equilibrium has $\alpha = a_u/a_v$ a real root of (18), there is at most one.
--
--   **Formalization Note** The cubic is Mathlib's `Cubic ℝ`, whose `discr` is the classical discriminant above; the statement also records that its polynomial evaluates to $f$.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), p. 56 (PDF 55), proof of Proposition 1, the displayed discriminant Δ and 'which is negative. Thus, there exists a unique real root'

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Proof of Proposition 1, p. 56 (PDF 55): the discriminant of the cubic (18) is the printed
expression Δ = −τ_ε(…), which is negative, so f has a unique real root. -/
theorem uniqueness_discriminant (P : Params) (hP : P.Standing) :
    (∀ x : ℝ, (cubic18 P).toPoly.eval x = cubicF P x) ∧
    (cubic18 P).discr = -P.teps *
      (4 * P.te ^ 3 * P.teta ^ 4 + 4 * P.te ^ 4 * P.teta ^ 3 + 4 * P.te * P.tu ^ 3 * P.teps ^ 3
        + 4 * P.te ^ 3 * P.tu * P.teps ^ 3 + 4 * P.te ^ 4 * P.tu * P.teps ^ 2
        + 27 * P.te ^ 4 * P.tu ^ 2 * P.teps
        + 12 * P.te ^ 3 * P.teps * P.teta ^ 3 + 4 * P.te ^ 3 * P.teps ^ 3 * P.teta
        + 8 * P.te ^ 4 * P.teps * P.teta ^ 2 + 4 * P.te ^ 4 * P.teps ^ 2 * P.teta
        + 4 * P.tu ^ 3 * P.teps ^ 3 * P.teta + 8 * P.te ^ 2 * P.tu ^ 2 * P.teps ^ 3
        + 36 * P.te ^ 3 * P.tu ^ 2 * P.teps ^ 2 + 12 * P.te ^ 3 * P.teps ^ 2 * P.teta ^ 2
        + 12 * P.te * P.tu ^ 2 * P.teps ^ 2 * P.teta ^ 2
        + 24 * P.te ^ 2 * P.tu * P.teps ^ 2 * P.teta ^ 2
        + 27 * P.te ^ 2 * P.tu ^ 2 * P.teps * P.teta ^ 2
        + 48 * P.te ^ 2 * P.tu ^ 2 * P.teps ^ 2 * P.teta
        + 36 * P.te ^ 4 * P.tu * P.teps * P.teta
        + 12 * P.te * P.tu ^ 2 * P.teps ^ 3 * P.teta
        + 12 * P.te ^ 2 * P.tu * P.teps * P.teta ^ 3
        + 12 * P.te ^ 2 * P.tu * P.teps ^ 3 * P.teta
        + 48 * P.te ^ 3 * P.tu * P.teps * P.teta ^ 2
        + 52 * P.te ^ 3 * P.tu * P.teps ^ 2 * P.teta
        + 54 * P.te ^ 3 * P.tu ^ 2 * P.teps * P.teta) ∧
    (cubic18 P).discr < 0 ∧
    ∀ x y : ℝ, cubicF P x = 0 → cubicF P y = 0 → x = y := by sorry
end CostlyPriceInterp.MarketEq
