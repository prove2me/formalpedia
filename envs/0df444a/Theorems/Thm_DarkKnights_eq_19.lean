-- Prove2me | Theorems.Thm_DarkKnights_eq_19
-- name    : DarkKnights.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:43.625052+00:00
-- url     : https://prove2.me/theorems/82786686-d245-49b4-9e32-0f7d9b4fe1c8
-- title:
--   Eqs. (18)–(19) — for $h\le1/2$ the dealer never injects and $M=\int_{z_R}^{Z}hb\,d\Gamma$
-- statement:
--   Let $\alpha\in(0,1)$, $Z>0$, $k>0$, $b\ge0$ and $0\le h\le1/2$, and let $\sigma$ be any dealer-optimal strategy. With $z_R=hb/k^\alpha$, the CDS premium is $\int_0^{z_R}hb\,d\Gamma(z)$ (the premium of (18)), and the value of debt is
--   $$
--   M(k,b,h)=\int_{z_R}^{Z}hb\,d\Gamma(z).\qquad(19)
--   $$
--
--   This is the value of debt for low hedge ratios, used in footnote 17 to show that the lender prefers full hedging.
--
--   Differences from the source:
--   - generalization: the value under the dealer's strategy of Lemmas 2–3 (Appendices A, D for other hedge ratios) → the value under every dealer-optimal strategy $\sigma$; reason: the paper's strategy is dealer-optimal, so this specializes to it; all optimal offers give every player the same payoff except at the indifference point $a=b-hb$, a null set of states (at $h\ge1$, $a\ge b$ the dealer is indifferent among offers with identical payoffs)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
--   - encoding: integrals $\int_x^y \cdots d\Gamma(z)$ with $z\sim U[0,Z]$ → $(1/Z)\times$ set integrals over subsets of $[0,Z]$ (empty when a threshold exceeds $Z$); reason: Lean convention; $\Gamma$ has no mass outside $[0,Z]$, so the same numbers in every instance
--   - encoding: $z_R=hb/k^\alpha$ → hypothesis $k>0$; reason: the expression is undefined at $k=0$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, Appendix E, eqs. (18)–(19), p.45 (PDF 47)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

open MeasureTheory

namespace DarkKnights

/-- **Eqs. (18)–(19)** (the value of debt in the active-CDS-seller model, `h ≤ 1/2`).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, Appendix E, eqs. (18)–(19), p.45 (PDF p.47).

For `0 ≤ h ≤ 1/2`, `k > 0`, `b ≥ 0` and every dealer-optimal strategy `σ`, with
`z_R = h b/k^α`: the CDS premium is `∫_0^{z_R} h b dΓ` (the bracket of (18)) and the value of
debt is `M(k, b, h) = ∫_{z_R}^{Z} h b dΓ` (19).

**Formalization Note** Set integrals over `[0, Z] ∩ [0, z_R)` and `[0, Z] ∩ [z_R, ∞)`, as in
Lemma 4. -/
theorem eq_19 (α Z k b h : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hk : 0 < k)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (σ : ℝ → ℝ × ℝ)
    (hσ : IsDealerOptimal α Z k b h σ) :
    let zR : ℝ := h * b / k ^ α
    premium2 α Z k b h σ = (1 / Z) * (∫ z in Set.Icc (0 : ℝ) Z ∩ {z | z < zR}, h * b) ∧
      debtValue2 α Z k b h σ = (1 / Z) * ∫ z in Set.Icc (0 : ℝ) Z ∩ {z | zR ≤ z}, h * b := by sorry

end DarkKnights
