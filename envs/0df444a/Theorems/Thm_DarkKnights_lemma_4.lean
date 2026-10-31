-- Prove2me | Theorems.Thm_DarkKnights_lemma_4
-- name    : DarkKnights.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:39.009673+00:00
-- url     : https://prove2.me/theorems/7801882b-0adc-42e1-a821-b9aa1bf22ce3
-- title:
--   Lemma 4 — for $h>1/2$, $M(k,b,h)=\int_{z_L}^{z_R}a\,d\Gamma+\int_{z_R}^{Z}hb\,d\Gamma$ (13)
-- statement:
--   Let $\alpha\in(0,1)$, $Z>0$, $k>0$, $b\ge0$ and $1/2<h\le1$, and let $\sigma$ be any dealer-optimal strategy. With $a=zk^\alpha$, $z\sim U[0,Z]$,
--   $$
--   z_L=\frac{b-hb}{k^\alpha},\qquad z_R=\frac{hb}{k^\alpha},
--   $$
--   the CDS premium is
--   $$
--   \int_0^{z_L}hb\,d\Gamma(z)+\int_{z_L}^{z_R}(b-a)\,d\Gamma(z),
--   $$
--   and the value of debt is
--   $$
--   M(k,b,h)=\int_{z_L}^{z_R}a\,d\Gamma(z)+\int_{z_R}^{Z}hb\,d\Gamma(z).\qquad(13)
--   $$
--
--   The premium compensates the dealer for the CDS payment in the liquidation states and for the equity injection in the intermediate states; (13) is the input of the lender's choice of hedge ratio.
--
--   Differences from the source:
--   - generalization: the value under the dealer's strategy of Lemmas 2–3 (Appendices A, D for other hedge ratios) → the value under every dealer-optimal strategy $\sigma$; reason: the paper's strategy is dealer-optimal, so this specializes to it; all optimal offers give every player the same payoff except at the indifference point $a=b-hb$, a null set of states (at $h\ge1$, $a\ge b$ the dealer is indifferent among offers with identical payoffs)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
--   - encoding: integrals $\int_x^y \cdots d\Gamma(z)$ with $z\sim U[0,Z]$ → $(1/Z)\times$ set integrals over subsets of $[0,Z]$ (empty when a threshold exceeds $Z$); reason: Lean convention; $\Gamma$ has no mass outside $[0,Z]$, so the same numbers in every instance
--   - reading: the case $h>1/2$ (p.18) → $1/2<h\le1$; reason: §2's standing conjecture $h\le1$ (p.15); for $h>1$ the value is that of Appendix A
--   - encoding: $z_L=(b-hb)/k^\alpha$, $z_R=hb/k^\alpha$ → hypothesis $k>0$; reason: the expression is undefined at $k=0$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, Lemma 4 and eq. (13), p.19 (PDF 21); proof Appendix E, pp.44–46 (PDF 46–48)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

open MeasureTheory

namespace DarkKnights

/-- **Lemma 4**, eq. (13) (the value of debt in the active-CDS-seller model, `h > 1/2`).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, Lemma 4 and eq. (13), p.19 (PDF p.21); proof Appendix E,
pp.44–46 (PDF pp.46–48).

For `1/2 < h ≤ 1`, `k > 0`, `b ≥ 0` and **every** dealer-optimal strategy `σ`, with
`z_L = (b − h b)/k^α` and `z_R = h b/k^α`:
* the CDS premium is `∫_0^{z_L} h b dΓ + ∫_{z_L}^{z_R} (b − a) dΓ` (the bracket of the first
  display), and
* the value of debt is `M(k, b, h) = ∫_{z_L}^{z_R} a dΓ + ∫_{z_R}^{Z} h b dΓ` (13),

where `a = z k^α` and `dΓ = dz / Z` on `[0, Z]`.

**Formalization Note** The paper's integrals are set integrals over `[0, Z] ∩ [z_L, z_R)`,
`[0, Z] ∩ [0, z_L)` and `[0, Z] ∩ [z_R, ∞)`: `Γ` has no mass beyond `Z`, so when `z_R > Z` the
last one is empty (never a reversed interval integral). -/
theorem lemma_4 (α Z k b h : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hk : 0 < k)
    (hb : 0 ≤ b) (hh : 1 / 2 < h) (hh1 : h ≤ 1) (σ : ℝ → ℝ × ℝ)
    (hσ : IsDealerOptimal α Z k b h σ) :
    let zL : ℝ := (b - h * b) / k ^ α
    let zR : ℝ := h * b / k ^ α
    premium2 α Z k b h σ =
        (1 / Z) * ((∫ z in Set.Icc (0 : ℝ) Z ∩ {z | z < zL}, h * b)
          + ∫ z in Set.Icc (0 : ℝ) Z ∩ {z | zL ≤ z ∧ z < zR}, (b - z * k ^ α)) ∧
      debtValue2 α Z k b h σ =
        (1 / Z) * ((∫ z in Set.Icc (0 : ℝ) Z ∩ {z | zL ≤ z ∧ z < zR}, z * k ^ α)
          + ∫ z in Set.Icc (0 : ℝ) Z ∩ {z | zR ≤ z}, h * b) := by sorry

end DarkKnights
