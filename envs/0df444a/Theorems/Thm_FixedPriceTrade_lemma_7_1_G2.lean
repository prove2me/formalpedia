-- Prove2me | Theorems.Thm_FixedPriceTrade_lemma_7_1_G2
-- name    : FixedPriceTrade.lemma_7_1_G2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:43.512715+00:00
-- url     : https://prove2.me/theorems/4921d7e7-ae18-4edd-ae74-76b9b2876841
-- title:
--   Lemma 7.1, (G2) — the endpoint envelope and its unique maximum at $C_d$
-- statement:
--   Let $d>0$ and let $C_d\in(1/4,1/2)$ satisfy $\tau(C_d)=d$. Then $C_d<\bar C(d)$ and, for every $C\in(0,\bar C(d))$,
--   $$
--   \Phi_d(x(C))=C\,\mathcal I_C(Y_d(C))-\frac{C^2Y_d(C)}{1-CY_d(C)},\qquad \frac{d}{dC}\Phi_d(x(C))=-\frac{(Y_d(C)+U_d(C))\,\mathcal B_d(C)}{(1-CY_d(C))^2},
--   $$
--   $$
--   \Phi_d(x(C_d))-\Phi_d(x(C))=\int_{\min\{C,C_d\}}^{\max\{C,C_d\}}\frac{(Y_d(u)+U_d(u))\,|\mathcal B_d(u)|}{(1-uY_d(u))^2}\,du .
--   $$
--   The envelope has a unique maximum at $C=C_d$.
--
--   Concavity at a fixed endpoint does not give global optimality; this envelope identity, over the whole branch including $C\le1/4$ and $C\ge1/2$, does.
--
--   Differences from the source:
--   - encoding: C_d (the unique root of τ(C) = d, (8)) → hypotheses C_d ∈ (1/4, 1/2) and τ(C_d) = d; reason: names C_d as in Theorem C; (7)–(8) give its existence
--   - encoding: unique maximum at C = C_d → C_d < C̄(d) and Φ_d(x(C)) < Φ_d(x(C_d)) for C ≠ C_d in (0, C̄(d)); reason: a unique maximizer on the branch
--   - encoding: d/dC Φ_d(x(C)) → HasDerivAt of C ↦ Φ_d(x(C)); reason: Mathlib's derivative
--   - encoding: the integral Φ_d(x(C)) = F_d[P_{x(C)}] → the integral Φ_d(x(C)) = F_d[P_{x(C)}], with its integrand stated integrable on (0, ∞); reason: the paper's integrands are bounded with compact support; the conjunct rules out a Bochner 0 for a non-integrable function, and adds no assumption
--   - encoding: the reference curve P_x indexed by its endpoint x → refCurve d C indexed by the curvature parameter C, with endpoint x(C); C = 0 is the limiting endpoint x = 1/d, P ≡ 1/d (p.16); reason: Lemma 6.1 makes C ↦ x(C) a bijection of (0, C̄(d)) onto (0, 1/d), and p.16 sets the endpoint x = 1/d at C = 0
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 7.1, (G2), p.16

import Mathlib
import Definitions.Def_FixedPriceTrade_refCurve

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Lemma 7.1 (nonnegative gaps), (G2)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.16.

Let `d > 0` and `C_d ∈ (1/4, 1/2)` with `τ(C_d) = d`. Then `C_d < C̄(d)`, and for every
`C ∈ (0, C̄(d))`: the energy `Φ_d(x(C)) = F_d[P_{x(C)}]` is a genuine integral and equals
`C I_C(Y_d(C)) − C² Y_d(C)/(1 − C Y_d(C))`; its derivative in `C` is
`−(Y_d + U_d) B_d/(1 − C Y_d)²`;
`Φ_d(x(C_d)) − Φ_d(x(C)) = ∫_{min{C, C_d}}^{max{C, C_d}} (Y_d(u) + U_d(u))|B_d(u)|/(1 − uY_d(u))² du`;
and the envelope has a unique maximum at `C_d`.

**Formalization Note.** `C` ranges over the whole branch `(0, C̄(d))`, including `C ≤ 1/4` and
`C ≥ 1/2`. -/
theorem lemma_7_1_G2 (d : ℝ) (hd : 0 < d) (Cd : ℝ) (hCd : Cd ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hτ : tauCurve Cd = d) :
    Cd < Cbar d ∧
    ∀ C ∈ Ioo 0 (Cbar d),
      IntegrableOn (fun a => d ^ 2 - 1 / refCurve d C a ^ 2 -
        a * deriv (fun b => Real.log (refCurve d C b)) a ^ 2) (Ioi 0) ∧
      Phi d C = C * ICrun C (Yd d C) - C ^ 2 * Yd d C / (1 - C * Yd d C) ∧
      HasDerivAt (Phi d) (-(Yd d C + Ud d C) * Bd d C / (1 - C * Yd d C) ^ 2) C ∧
      Phi d Cd - Phi d C = ∫ u in (min C Cd)..(max C Cd), envelopeIntegrand d u ∧
      (C ≠ Cd → Phi d C < Phi d Cd) := by sorry

end FixedPriceTrade
