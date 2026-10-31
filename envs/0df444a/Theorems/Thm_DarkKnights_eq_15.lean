-- Prove2me | Theorems.Thm_DarkKnights_eq_15
-- name    : DarkKnights.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:49.818998+00:00
-- url     : https://prove2.me/theorems/b6cd93a1-9df1-445f-a87b-c4a95e58a286
-- title:
--   Eq. (15) — with an intervening dealer, $V(k,b,1)=-k+\int_0^Z zk^\alpha d\Gamma-\tau\int_{z_R}^Z(zk^\alpha-b)d\Gamma$
-- statement:
--   Let $\alpha\in(0,1)$, $Z>0$, $\tau\in[0,1)$, $k>0$ and $b\ge0$, and let $\sigma$ be any dealer-optimal strategy at $h=1$. With $z_R=b/k^\alpha$,
--   $$
--   V(k,b,h)\big|_{h=1}=-k+\int_0^Z zk^\alpha\,d\Gamma(z)-\tau\int_{z_R}^{Z}(zk^\alpha-b)\,d\Gamma(z).\qquad(15)
--   $$
--
--   Compared with (7), liquidation losses have disappeared: the firm keeps the whole expected asset value, and only taxes on the equity payoff remain.
--
--   Differences from the source:
--   - generalization: the value under the dealer's strategy of Lemmas 2–3 (Appendices A, D for other hedge ratios) → the value under every dealer-optimal strategy $\sigma$; reason: the paper's strategy is dealer-optimal, so this specializes to it; all optimal offers give every player the same payoff except at the indifference point $a=b-hb$, a null set of states (at $h\ge1$, $a\ge b$ the dealer is indifferent among offers with identical payoffs)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
--   - encoding: integrals $\int_x^y \cdots d\Gamma(z)$ with $z\sim U[0,Z]$ → $(1/Z)\times$ set integrals over subsets of $[0,Z]$ (empty when a threshold exceeds $Z$); reason: Lean convention; $\Gamma$ has no mass outside $[0,Z]$, so the same numbers in every instance
--   - encoding: $z_R=b/k^\alpha$ → hypothesis $k>0$; reason: the expression is undefined at $k=0$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, eq. (15), p.20 (PDF 22)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

open MeasureTheory

namespace DarkKnights

/-- **Eq. (15)** (firm value at `h = 1` in the active-CDS-seller model).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, eq. (15), p.20 (PDF p.22).

For `k > 0`, `b ≥ 0` and every dealer-optimal strategy `σ` at `h = 1`, with `z_R = b/k^α`:
`V(k, b, 1) = −k + ∫_0^Z z k^α dΓ − τ ∫_{z_R}^{Z} (z k^α − b) dΓ`.

**Formalization Note** `dΓ = dz/Z` on `[0, Z]`; the last integral is over
`[0, Z] ∩ [z_R, ∞)` (empty when `z_R > Z`). -/
theorem eq_15 (α Z τ k b : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) (hk : 0 < k) (hb : 0 ≤ b) (σ : ℝ → ℝ × ℝ)
    (hσ : IsDealerOptimal α Z k b 1 σ) :
    firmValue2 α Z τ k b 1 σ =
      -k + (1 / Z) * (∫ z in Set.Icc (0 : ℝ) Z, z * k ^ α)
        - τ * ((1 / Z) * ∫ z in Set.Icc (0 : ℝ) Z ∩ {z | b / k ^ α ≤ z}, (z * k ^ α - b)) := by sorry

end DarkKnights
