-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_stage_revenue_gap
-- name    : BesbesZeevi.SingleParam.stage_revenue_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:37:47.227747+00:00
-- url     : https://prove2.me/theorems/9fad227d-e3ff-449f-8c1a-498d9872e35a
-- title:
--   Per-stage revenue gap: $r(p^D)-\mathbb E\,r(\hat p_i)\le C_2/(n\Delta^{(i-1)}_n)^{1/2}$
-- statement:
--   Fix a market, a family and a selection, and run Algorithm 3 with the tuning (19)–(20). There are $C_2>0$ and $n_0$ such that for every unit-rate Poisson process on a probability space, every $n\ge n_0$, every $\theta^*\in\Theta$ and every stage $i=2,\dots,\ell_n$,
--
--   $$
--   r(\lambda(p^D;\theta^*);\theta^*)-\mathbb E\big[r(\lambda(\hat p_i;\theta^*);\theta^*)\big]\le\frac{C_2}{(n\Delta^{(i-1)}_n)^{1/2}},
--   $$
--
--   where $r(\lambda(p;\theta^*);\theta^*)=p\lambda(p;\theta^*)$ and $p^D=p^D(\theta^*)$. The price of stage $i$ is computed from the estimate of stage $i-1$, so its expected revenue loss decays with the expected demand $n\Delta^{(i-1)}_n$ observed in that stage.
--
--   **Formalization Note** The constants are uniform in $\theta^*$ and $n$. The paper states the bound inside the proof of Proposition 5 without a range for $n$; "for all $n\ge n_0$" is the reading used by the $O(\cdot)$ conclusion.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 35 (PDF p. 37), proof of Proposition 5 (unnumbered display after (A-27))

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning
import Definitions.Def_BesbesZeevi_SingleParam_Algorithm

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- Per-stage revenue gap (Besbes–Zeevi 2009, proof of Proposition 5, p. 35): under the tuning
(19)–(20), for some `C₂ > 0` and all large `n`, uniformly in `θ* ∈ Θ` and `i = 2, …, ℓ_n`,
`r(λ(p^D; θ*); θ*) - E[r(λ(p̂_i; θ*); θ*)] ≤ C₂ / (n Δ^{(i-1)}_n)^{1/2}`. -/
theorem stage_revenue_gap (D : Market) (F : Family D) (σ : Selection D F) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ n₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : PoissonProcess Ω P), ∀ n : ℕ, n₀ ≤ n → ∀ θ ∈ F.Θ,
        ∀ i ∈ Finset.Icc 2 (numStages n),
          σ.pD θ * F.lam (σ.pD θ) θ
            - (∫⁻ ω, ENNReal.ofReal
                (stagePrice D F σ n (stageLength D.T n) θ (fun t => N.N t ω) i *
                  F.lam (stagePrice D F σ n (stageLength D.T n) θ (fun t => N.N t ω) i) θ)
                ∂P).toReal
            ≤ C₂ / Real.sqrt ((n : ℝ) * stageLength D.T n (i - 1)) := by sorry

end BesbesZeevi.SingleParam
