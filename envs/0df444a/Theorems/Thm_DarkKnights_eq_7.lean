-- Prove2me | Theorems.Thm_DarkKnights_eq_7
-- name    : DarkKnights.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:48.811307+00:00
-- url     : https://prove2.me/theorems/1051e224-5110-4625-9910-97462911537a
-- title:
--   Eq. (7) — active CDS buyer, $V(k,b,1)=-k+\int_{z_R}^Z zk^\alpha d\Gamma-\tau\int_{z_R}^Z(zk^\alpha-b)d\Gamma$
-- statement:
--   In the active-CDS-buyer model, let $\alpha\in(0,1)$, $Z>0$, $\tau\in[0,1)$, $k>0$ and $b\ge0$. With $z_R=b/k^\alpha$,
--   $$
--   V(k,b,h)\big|_{h=1}=-k+\int_{z_R}^{Z}zk^\alpha\,d\Gamma(z)-\tau\int_{z_R}^{Z}(zk^\alpha-b)\,d\Gamma(z).\qquad(7)
--   $$
--
--   The asset value of the states below $z_R$ is lost in liquidation; this loss is what the intervening dealer removes in (15).
--
--   Differences from the source:
--   - encoding: integrals $\int_x^y \cdots d\Gamma(z)$ with $z\sim U[0,Z]$ → $(1/Z)\times$ set integrals over subsets of $[0,Z]$ (empty when a threshold exceeds $Z$); reason: Lean convention; $\Gamma$ has no mass outside $[0,Z]$, so the same numbers in every instance
--   - encoding: $z_R=b/k^\alpha$ → hypothesis $k>0$; reason: the expression is undefined at $k=0$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §1, eq. (7), p.12 (PDF 14)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveBuyerModel

open MeasureTheory

namespace DarkKnights

/-- **Eq. (7)** (firm value at `h = 1` in the active-CDS-buyer model).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §1, eq. (7), p.12 (PDF p.14).

For `k > 0` and `b ≥ 0`, with `z_R = b/k^α`:
`V(k, b, 1) = −k + ∫_{z_R}^{Z} z k^α dΓ − τ ∫_{z_R}^{Z} (z k^α − b) dΓ`.

**Formalization Note** `dΓ = dz/Z` on `[0, Z]`; both integrals are over `[0, Z] ∩ [z_R, ∞)`
(empty when `z_R > Z`). -/
theorem eq_7 (α Z τ k b : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) (hk : 0 < k) (hb : 0 ≤ b) :
    firmValue1 α Z τ k b 1 =
      -k + (1 / Z) * (∫ z in Set.Icc (0 : ℝ) Z ∩ {z | b / k ^ α ≤ z}, z * k ^ α)
        - τ * ((1 / Z) * ∫ z in Set.Icc (0 : ℝ) Z ∩ {z | b / k ^ α ≤ z}, (z * k ^ α - b)) := by sorry

end DarkKnights
