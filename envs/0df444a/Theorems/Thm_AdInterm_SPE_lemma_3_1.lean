-- Prove2me | Theorems.Thm_AdInterm_SPE_lemma_3_1
-- name    : AdInterm.SPE.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:18.377597+00:00
-- url     : https://prove2.me/theorems/db478d5b-47b0-4aab-b565-e48e9c18d42e
-- title:
--   Lemma 3.1, p. 17 — facing a second-price auction with reserve r_S ≤ sup 𝒱 and competing bid D, (z_V, ψ_V) is an optimal mechanism in M
-- statement:
--   Consider one intermediary $I_\ell$ with $m\ge1$ buyers (Figure 3) whose values are i.i.d. with law $V$: nonnegative, lower support end $0$, finite mean, a continuous strictly positive density on the support, and a strictly increasing virtual value $\phi_V$. The intermediary bids in a second-price auction run by the seller with reserve $0\le r_S\le\sup\mathcal V$, against a random competing bid $D\ge0$ independent of the buyers.
--
--   With a mechanism $(r,Y)\in\mathcal M$ and highest buyer value $w$, the intermediary wins iff $w\ge r$ and $Y(w)\ge P:=\max(r_S,D)$; it then pays $P$ and charges its winning buyer $\max\big(r,Y^{-1}(P),V^{\mathrm{SH}(m)}\big)$. Its expected profit is $\Pi(r,Y)$. Then $(z_V,\psi_V)\in\mathcal M$ and
--
--   $$
--   \Pi(r,Y)\le\Pi(z_V,\psi_V)\qquad\text{for every }(r,Y)\in\mathcal M,
--   $$
--
--   that is, $Y^*(v)=\psi_V(v)$ and $r^*=z_V$ form an optimal mechanism for $I_\ell$ in $\mathcal M$.
--
--   This is the one-stage building block of the backward induction in Theorem 3.1; the optimal mechanism does not depend on $r_S$ or on the law of $D$.
--
--   **Formalization Note** $D$ has an arbitrary probability law on $[0,\infty)$ and is independent of the buyers (product measure); the page says only "a random competing bid $D$ with support $\mathcal D$". A report equal to $\max(r_S,D)$ wins, as in the seller's set $\Theta$ of Definition A.1. $r_S\le\sup\mathcal V$ is stated as $G_V(x)<1$ for all $x<r_S$. With one buyer the second-highest value is $0$. Expected profit is a single Bochner integral; no integrability is assumed of a deviation.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), Lemma 3.1, p. 17; proof pp. 35–36

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

open MeasureTheory

namespace AdInterm.SPE

theorem lemma_3_1 (m : ℕ) (hm : 1 ≤ m)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (hη : η (Set.Iio 0) = 0)
    (rS : ℝ) (hrS0 : 0 ≤ rS)
    (hrS : ∀ x, x < rS → cdf μ x < 1) :
    IsMech (zproj μ, psi μ) ∧
      ∀ mech : Mechanism, IsMech mech →
        singleProfit m μ η rS mech ≤
          singleProfit m μ η rS (zproj μ, psi μ) := by sorry

end AdInterm.SPE
