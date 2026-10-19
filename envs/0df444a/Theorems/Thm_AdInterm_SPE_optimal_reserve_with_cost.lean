-- Prove2me | Theorems.Thm_AdInterm_SPE_optimal_reserve_with_cost
-- name    : AdInterm.SPE.optimal_reserve_with_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:28.648278+00:00
-- url     : https://prove2.me/theorems/54e482d3-5183-45db-abb9-998e1e34d486
-- title:
--   Proof of Lemma 3.1, Step 2, p. 36 — with seller cost c ≤ sup 𝒱, the reserve φ_V^{-1}(c) is optimal in a second-price auction with m i.i.d. bidders
-- statement:
--   Let $m\ge1$ buyers have i.i.d. values with law $V$, where $V$ is nonnegative with lower support end $0$, finite mean, a continuous strictly positive density on its support and a strictly increasing virtual value $\phi_V$. Let $V^{\mathrm{FH}(m)}$ and $V^{\mathrm{SH}(m)}$ be the highest and second-highest values ($V^{\mathrm{SH}(1)}=0$). A seller with cost $c$, $0\le c\le\sup\mathcal V$, runs a second-price auction with reserve $\delta\ge0$, earning
--
--   $$
--   R_c(\delta)=\mathbb E\big[(\max(\delta,V^{\mathrm{SH}(m)})-c)\,\mathbf 1\{V^{\mathrm{FH}(m)}\ge\delta\}\big].
--   $$
--
--   Then $\phi_V^{-1}(c)\ge0$ and $R_c(\delta)\le R_c\big(\phi_V^{-1}(c)\big)$ for every $\delta\ge0$: the reserve $\delta=\phi_V^{-1}(c)$ is optimal.
--
--   In the paper this is the pointwise optimization, for each realized upstream price $P_\ell=c$, that reduces the intermediary's problem in Lemma 3.1 to choosing a reserve.
--
--   **Formalization Note** $c\le\sup\mathcal V$ is stated as $G_V(x)<1$ for every $x<c$. $\phi_V^{-1}(c)=\inf\{x>0: G_V(x)<1\Rightarrow\phi_V(x)\ge c\}$, so at $c=\sup\mathcal V<\infty$ it equals $\sup\mathcal V$.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), proof of Lemma 3.1, Step 2, p. 36

import Mathlib
import Definitions.Def_AdInterm_SPE_VirtualValue

open MeasureTheory

namespace AdInterm.SPE

theorem optimal_reserve_with_cost (m : ℕ) (hm : 1 ≤ m)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ x, x < c → cdf μ x < 1) :
    0 ≤ phiInv μ c ∧
      ∀ δ : ℝ, 0 ≤ δ → reserveObj m μ c δ ≤ reserveObj m μ c (phiInv μ c) := by sorry

end AdInterm.SPE
