-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_overflow_bound
-- name    : BesbesZeevi.SingleParam.overflow_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:38:04.483579+00:00
-- url     : https://prove2.me/theorems/8e4249af-f766-4b10-8e5c-d26fbf7e55c4
-- title:
--   Overflow bound: $\mathbb E[(Y_n-nx)^+]\le nC_8(\log n)^{1/2}n^{a_{\ell_n}-1}$
-- statement:
--   Fix a market, a family and a selection, and run Algorithm 3 with the tuning (19)–(20). Let $Y_n=N(X^{\ell_n}_n)$ be the total demand requested over the horizon (uncapped). There are $C_8>0$ and $n_0$ such that for every unit-rate Poisson process on a probability space, every $n\ge n_0$ and every $\theta^*\in\Theta$ with $\lambda(\overline p;\theta^*)\le x/T$,
--
--   $$
--   \mathbb E\big[(Y_n-nx)^+\big]\le nC_8(\log n)^{1/2}n^{a_{\ell_n}-1}.
--   $$
--
--   When the full-information price does not exhaust the inventory before $T$ (the case $\lambda(\overline p;\theta^*)\le x/T$), the expected excess demand over the inventory is a vanishing fraction of $n$.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of $(Y_n-nx)^+$, converted to a real number; $Y_n$ is bounded by $N(nMT)$, which has finite mean. The constants are uniform in $\theta^*$.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 36 (PDF p. 38), proof of Proposition 5 (unnumbered display at the end of the page)

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning
import Definitions.Def_BesbesZeevi_SingleParam_Algorithm

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- Overflow bound (Besbes–Zeevi 2009, proof of Proposition 5, p. 36): in the case
`λ(p̄; θ*) ≤ x/T`, under the tuning (19)–(20), for some `C₈ > 0` and all large `n`,
uniformly in `θ*`, the total demand `Y_n = N(X^{ℓ_n}_n)` satisfies
`E[(Y_n - n x)^+] ≤ n C₈ (log n)^{1/2} n^{a_{ℓ_n} - 1}`. -/
theorem overflow_bound (D : Market) (F : Family D) (σ : Selection D F) :
    ∃ C₈ : ℝ, 0 < C₈ ∧ ∃ n₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : PoissonProcess Ω P), ∀ n : ℕ, n₀ ≤ n → ∀ θ ∈ F.Θ,
        F.lam D.pHi θ ≤ D.x / D.T →
          (∫⁻ ω, ENNReal.ofReal
              ((N.N (cumIntensity D F σ n (stageLength D.T n) θ (fun t => N.N t ω)
                  (numStages n)) ω : ℝ) - (n : ℝ) * D.x) ∂P).toReal
            ≤ (n : ℝ) * C₈ * Real.sqrt (Real.log n)
                * (n : ℝ) ^ (aCoef (numStages n) - 1) := by sorry

end BesbesZeevi.SingleParam
