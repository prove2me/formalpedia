-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_price_deviation_A30
-- name    : BesbesZeevi.SingleParam.price_deviation_A30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:37:51.074673+00:00
-- url     : https://prove2.me/theorems/ea391514-339e-418c-b134-67d1e63cb4c6
-- title:
--   (A-30), corrected: the stage-$i$ demand rate exceeds $\lambda(p^c)$ by more than $C_5(\log n/(n\Delta^{(i-1)}_n))^{1/2}$ with probability $O(1/n)$
-- statement:
--   Fix a market, a family and a selection, and run Algorithm 3 with the tuning (19)–(20). Let $\eta=2$. There are $C_5,C_6>0$ and $n_0$ such that for every unit-rate Poisson process on a probability space, every $n\ge n_0$, every $\theta^*\in\Theta$ with $\lambda(\overline p;\theta^*)\le x/T$ and every stage $i=2,\dots,\ell_n$,
--
--   $$
--   \mathbb P\Big\{\lambda(\hat p_i;\theta^*)-\lambda(p^c;\theta^*)>\frac{C_5(\log n)^{1/2}}{(n\Delta^{(i-1)}_n)^{1/2}}\Big\}\le\frac{C_6}{n^{\eta-1}},
--   $$
--
--   where $p^c=p^c(\theta^*)$. In words, after the first stage the algorithm rarely prices so low that it sells markedly faster than the run-out rate $\lambda(p^c;\theta^*)$, which is what keeps the inventory from being exhausted early.
--
--   **Formalization Note** The paper prints the threshold $C_5/(\Delta^{(i-1)}_n)^{1/2}$ and then applies the bound with $C_6/(n\Delta^{(i-1)}_n)^{1/2}$. A threshold of order $(n\Delta^{(i-1)}_n)^{-1/2}$ without a logarithm is exceeded with probability bounded away from zero when $p^c(\theta^*)$ is interior (the estimation error is of exactly that order and has either sign), so the statement used here follows the cited argument (B-10), whose threshold carries the factor $(\log n)^{1/2}$. The subsequent overflow argument goes through with this threshold.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 36 (PDF p. 38), proof of Proposition 5, eq. (A-30); cf. p. 42 (PDF p. 44), (B-10)

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning
import Definitions.Def_BesbesZeevi_SingleParam_Algorithm

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- (A-30), corrected (Besbes–Zeevi 2009, proof of Proposition 5, p. 36): in the case
`λ(p̄; θ*) ≤ x/T`, under the tuning (19)–(20), with `η = 2`, for some `C₅, C₆ > 0` and all
large `n`, uniformly in `θ*` and `i = 2, …, ℓ_n`,
`P{λ(p̂_i; θ*) - λ(p^c; θ*) > C₅ (log n)^{1/2} / (n Δ^{(i-1)}_n)^{1/2}} ≤ C₆ / n^{η-1}`.
The printed threshold `C₅/(Δ^{(i-1)}_n)^{1/2}` is replaced by the one the proof uses (the
next display's `n Δ^{(i-1)}_n`, with the `(log n)^{1/2}` of the cited (B-10)). -/
theorem price_deviation_A30 (D : Market) (F : Family D) (σ : Selection D F) :
    ∃ C₅ : ℝ, 0 < C₅ ∧ ∃ C₆ : ℝ, 0 < C₆ ∧ ∃ n₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : PoissonProcess Ω P), ∀ n : ℕ, n₀ ≤ n → ∀ θ ∈ F.Θ,
        F.lam D.pHi θ ≤ D.x / D.T →
        ∀ i ∈ Finset.Icc 2 (numStages n),
          (P {ω | F.lam (stagePrice D F σ n (stageLength D.T n) θ (fun t => N.N t ω) i) θ
                - F.lam (σ.pc θ) θ
              > C₅ * Real.sqrt (Real.log n)
                  / Real.sqrt ((n : ℝ) * stageLength D.T n (i - 1))}).toReal
            ≤ C₆ / (n : ℝ) ^ ((2 : ℝ) - 1) := by sorry

end BesbesZeevi.SingleParam
