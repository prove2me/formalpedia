-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_revenue_ratio_A31
-- name    : BesbesZeevi.SingleParam.revenue_ratio_A31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:38:14.975305+00:00
-- url     : https://prove2.me/theorems/0e856b39-540e-4c5f-802a-31862ff52574
-- title:
--   (A-31): $J^\pi_n/J^D_n\ge1-(C_9/m^D)[\ell_n n^{a_{\ell_n}-1}+(\log n)^{1/2}n^{a_{\ell_n}-1}]$
-- statement:
--   Fix a market, a family and a selection, and run Algorithm 3 with the tuning (19)–(20). Let $m^D=m\min\{T,x/M\}$ as in Fact 1. There are $C_9>0$ and $n_0$ such that for every unit-rate Poisson process on a probability space, every $n\ge n_0$ and every $\theta^*\in\Theta$ with $\lambda(\overline p;\theta^*)\le x/T$,
--
--   $$
--   \frac{J^\pi_n}{J^D_n}\ge1-\frac{C_9}{m^D}\Big[\ell_n n^{a_{\ell_n}-1}+(\log n)^{1/2}n^{a_{\ell_n}-1}\Big].
--   $$
--
--   This is the regret bound of Algorithm 3 in the case $\lambda(\overline p;\theta^*)\le x/T$, before the tuning exponents are evaluated.
--
--   **Formalization Note** The constants are uniform in $\theta^*$ and $n$. The case $\lambda(\overline p;\theta^*)>x/T$ is not covered by the paper's proof ("A similar result holds"), so it is not part of this item.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 37 (PDF p. 39), proof of Proposition 5, eq. (A-31)

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning
import Definitions.Def_BesbesZeevi_SingleParam_Algorithm

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- (A-31) (Besbes–Zeevi 2009, proof of Proposition 5, p. 37): in the case `λ(p̄; θ*) ≤ x/T`,
under the tuning (19)–(20), for some `C₉ > 0` and all large `n`, uniformly in `θ*`,
`J^π_n / J^D_n ≥ 1 - (C₉/m^D) [ℓ_n n^{a_{ℓ_n} - 1} + (log n)^{1/2} n^{a_{ℓ_n} - 1}]`, where
`m^D = m min {T, x/M}` (Fact 1). -/
theorem revenue_ratio_A31 (D : Market) (F : Family D) (σ : Selection D F) :
    ∃ C₉ : ℝ, 0 < C₉ ∧ ∃ n₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : PoissonProcess Ω P), ∀ n : ℕ, n₀ ≤ n → ∀ θ ∈ F.Θ,
        F.lam D.pHi θ ≤ D.x / D.T →
          1 - C₉ / (F.m * min D.T (D.x / F.M))
              * ((numStages n : ℝ) * (n : ℝ) ^ (aCoef (numStages n) - 1)
                + Real.sqrt (Real.log n) * (n : ℝ) ^ (aCoef (numStages n) - 1))
            ≤ expRevenue N D F σ n (numStages n) (stageLength D.T n) θ
                / detValueScaled D (fun p => F.lam p θ) n := by sorry

end BesbesZeevi.SingleParam
