-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_revenue_lower_bound_A2
-- name    : BesbesZeevi.Nonparametric.revenue_lower_bound_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:50:24.705536+00:00
-- url     : https://prove2.me/theorems/2687a5a6-7a91-41ef-b313-404c9275fd78
-- title:
--   (A-2): $J^\pi_n\ge\mathbb E\big[\hat p\min\{Y^{(P)}_n,(nx-Y^{(L)}_n)^+\}\big]$
-- statement:
--   Let $\lambda\in\mathcal L$, $n\ge1$, $\kappa\ge1$ and $\tau\in(0,T]$, and run Algorithm 1 $\pi(\tau,\kappa)$ in the market of size $n$, driven by a unit-rate Poisson process $N$. Let:
--
--   1. $Y^{(L)}_n=N(X^{(L)}_n)$ be the learning-phase requests, where $X^{(L)}_n=\sum_{i=1}^{\kappa}\lambda(p_i)n\Delta$;
--   2. $Y_n=N(X^{(L)}_n+X^{(P)}_n)$ be the total requests, where $X^{(P)}_n=\lambda(\hat p)n(T-\tau)$;
--   3. $Y^{(P)}_n=Y_n-Y^{(L)}_n$.
--
--   All three count requests as if stock never ran out. The expected revenue is at least the expected revenue of the pricing phase:
--
--   $$
--   J^\pi_n\ \ge\ \mathbb E\Big[\hat p\,\min\big\{Y^{(P)}_n,\ (\lfloor nx\rfloor-Y^{(L)}_n)^+\big\}\Big].
--   $$
--
--   This is the starting point of the proof of Proposition 1.
--
--   **Formalization Note** With integer sales the inventory is $\lfloor nx\rfloor$ units, so the paper's $(nx-Y^{(L)}_n)^+$ is read as $(\lfloor nx\rfloor-Y^{(L)}_n)^+$.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 28 (PDF 30), proof of Proposition 1, Step 1, eq. (A-2)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

/-- (A-2), proof of Proposition 1, Step 1, p. 28: the expected revenue of Algorithm 1 is at least
`E[p̂ min{Y^{(P)}_n, (⌊n x⌋ - Y^{(L)}_n)^+}]`, the revenue of the pricing phase alone. -/
theorem revenue_lower_bound_A2 (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x)
    (hT : 0 < T) (lam : ℝ → ℝ) (hlam : L.Mem P lam) {Ω : Type*} [MeasureSpace Ω]
    (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) (κ : ℕ)
    (hτ : 0 < τ) (hτT : τ ≤ T) (hκ : 1 ≤ κ) :
    ∫ ω, phat P lam x T n τ κ N ω *
        min (((requestsTotal P lam x T n τ κ N ω : ℕ) : ℝ)
              - ((requestsLearn P lam n τ κ N ω : ℕ) : ℝ))
          (max ((salesCap n x : ℝ) - ((requestsLearn P lam n τ κ N ω : ℕ) : ℝ)) 0)
      ≤ expectedRevenue P lam x T n τ κ N := by sorry

end BesbesZeevi.Nonparametric
