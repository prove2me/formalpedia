-- Prove2me | Theorems.Thm_AdInterm_SPE_lemma_B_1
-- name    : AdInterm.SPE.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:12.017016+00:00
-- url     : https://prove2.me/theorems/41005db5-1921-4d24-aac8-ba1d677413ba
-- title:
--   Lemma B.1, pp. 44–45 — Lemma 3.1 for buyer values with an atom at zero: (z_V, ψ_V) is still an optimal mechanism in M
-- statement:
--   This is Lemma 3.1 when the buyers' values may be zero with positive probability. Let $V$ be nonnegative with an atom at $0$, $\mathbb P(V=0)>0$, absolutely continuous on $(0,\infty)$, with finite mean, and let its strictly positive part $V\mid V>0$ have a continuous, strictly positive density on its support (an interval with lower end $0$) and a strictly increasing virtual value $\phi_{V\mid V>0}$. Define $z_V$ and $\psi_V$ through $\phi_{V\mid V>0}$ (Definition 3.2).
--
--   One intermediary with $m\ge1$ buyers with i.i.d. values of law $V$ faces a second-price auction with reserve $0\le r_S\le\sup\mathcal V$ and an independent random competing bid $D\ge0$, as in Lemma 3.1. Then $(z_V,\psi_V)\in\mathcal M$ and
--
--   $$
--   \Pi(r,Y)\le\Pi(z_V,\psi_V)\qquad\text{for every }(r,Y)\in\mathcal M,
--   $$
--
--   so $Y^*(v)=\psi_V(v)$, $r^*=z_V$ is an optimal mechanism in $\mathcal M$.
--
--   Anticipated reports $W_t$, $t\ge1$, typically have an atom at zero, so this is the version of Lemma 3.1 used in the inductive step of Theorem 3.1.
--
--   **Formalization Note** The virtual value is computed from the cdf of $V$ at points $x>0$, where it coincides with $\phi_{V\mid V>0}(x)$. The conventions of Lemma 3.1 (independent $D$, ties with $\max(r_S,D)$ won, $r_S\le\sup\mathcal V$ as $G_V(x)<1$ for $x<r_S$) apply.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), e-companion B, Lemma B.1, pp. 44–45

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

open MeasureTheory

namespace AdInterm.SPE

theorem lemma_B_1 (m : ℕ) (hm : 1 ≤ m)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : RegularPos μ) (hatom : 0 < μ {0}) (hVinc : IncVV μ)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (hη : η (Set.Iio 0) = 0)
    (rS : ℝ) (hrS0 : 0 ≤ rS)
    (hrS : ∀ x, x < rS → cdf μ x < 1) :
    IsMech (zproj μ, psi μ) ∧
      ∀ mech : Mechanism, IsMech mech →
        singleProfit m μ η rS mech ≤
          singleProfit m μ η rS (zproj μ, psi μ) := by sorry

end AdInterm.SPE
