-- Prove2me | Theorems.Thm_DarkKnights_appendix_A
-- name    : DarkKnights.appendix_A
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:25.506382+00:00
-- url     : https://prove2.me/theorems/bca36e05-7327-4042-8c41-ca67fbace130
-- title:
--   Appendix A — for $h>1$ the value of debt $\int_0^{b/k^\alpha}a\,d\Gamma+\int_{b/k^\alpha}^{Z}b\,d\Gamma$ does not depend on $h$
-- statement:
--   Let $\alpha\in(0,1)$, $Z>0$, $k>0$, $b\ge0$ and $h>1$, and let $\sigma$ be any dealer-optimal strategy at $h$. Then the CDS premium is
--   $$
--   \int_0^{b/k^\alpha}(b-a)\,d\Gamma(z),
--   $$
--   the value of debt is
--   $$
--   M=\int_0^{b/k^\alpha}a\,d\Gamma(z)+\int_{b/k^\alpha}^{Z}b\,d\Gamma(z),
--   $$
--   and this equals the value of debt at $h=1$ under any dealer-optimal strategy at $h=1$. Hence the lender can do neither better nor worse by hedging beyond $1$.
--
--   This justifies the conjecture $h\le 1$ under which §2 is solved.
--
--   Differences from the source:
--   - reading: this expression does not depend on $h$; the debt holder cannot do better (nor worse) by increasing his hedge ratio beyond 1 → the value at $h>1$ equals the value at $h=1$ under every dealer-optimal strategy; reason: the comparison the sentence draws, made explicit
--   - generalization: the value under the dealer's strategy of Lemmas 2–3 (Appendices A, D for other hedge ratios) → the value under every dealer-optimal strategy $\sigma$; reason: the paper's strategy is dealer-optimal, so this specializes to it; all optimal offers give every player the same payoff except at the indifference point $a=b-hb$, a null set of states (at $h\ge1$, $a\ge b$ the dealer is indifferent among offers with identical payoffs)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
--   - encoding: integrals $\int_x^y \cdots d\Gamma(z)$ with $z\sim U[0,Z]$ → $(1/Z)\times$ set integrals over subsets of $[0,Z]$ (empty when a threshold exceeds $Z$); reason: Lean convention; $\Gamma$ has no mass outside $[0,Z]$, so the same numbers in every instance
--   - encoding: the threshold $b/k^\alpha$ → hypothesis $k>0$; reason: the expression is undefined at $k=0$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, Appendix A, final display and last sentence, pp.41–42 (PDF 43–44)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

open MeasureTheory

namespace DarkKnights

/-- **Appendix A** (hedge ratios above one do not change the value of debt).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, Appendix A, final display, pp.41–42 (PDF pp.43–44).

For `h > 1`, `k > 0`, `b ≥ 0` and every dealer-optimal strategy `σ` at `h`: the CDS premium is
`∫_0^{b/k^α} (b − a) dΓ` (the "upfront CDS premium" of the first display) and
`M = ∫_0^{b/k^α} a dΓ + ∫_{b/k^α}^{Z} b dΓ`, which does not depend on `h`; in particular it
equals the value of debt at `h = 1` under every dealer-optimal strategy `σ'` at `h = 1`.

**Formalization Note** Set integrals over `[0, Z] ∩ [0, b/k^α)` and `[0, Z] ∩ [b/k^α, ∞)`. -/
theorem appendix_A (α Z k b h : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hk : 0 < k)
    (hb : 0 ≤ b) (hh : 1 < h) (σ σ' : ℝ → ℝ × ℝ) (hσ : IsDealerOptimal α Z k b h σ)
    (hσ' : IsDealerOptimal α Z k b 1 σ') :
    premium2 α Z k b h σ =
        (1 / Z) * ∫ z in Set.Icc (0 : ℝ) Z ∩ {z | z < b / k ^ α}, (b - z * k ^ α) ∧
      debtValue2 α Z k b h σ =
        (1 / Z) * ((∫ z in Set.Icc (0 : ℝ) Z ∩ {z | z < b / k ^ α}, z * k ^ α)
          + ∫ z in Set.Icc (0 : ℝ) Z ∩ {z | b / k ^ α ≤ z}, b) ∧
      debtValue2 α Z k b h σ = debtValue2 α Z k b 1 σ' := by sorry

end DarkKnights
