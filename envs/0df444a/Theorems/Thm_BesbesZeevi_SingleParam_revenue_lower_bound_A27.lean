-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_revenue_lower_bound_A27
-- name    : BesbesZeevi.SingleParam.revenue_lower_bound_A27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:37:19.582684+00:00
-- url     : https://prove2.me/theorems/9c2e2e9f-e372-467f-9aa9-99f5927f9af6
-- title:
--   (A-27): revenue lower bound for Algorithm 3
-- statement:
--   Fix a market, a family with a selection, a unit-rate Poisson process on a probability space, $n\ge1$, $\ell\ge1$ stages with lengths $\Delta^{(i)}>0$ summing to $T$, and $\theta^*\in\Theta$. Write $r(p)=p\lambda(p;\theta^*)$ for the revenue rate, $p^D=p^D(\theta^*)$, $\hat p_i$ for the prices of Algorithm 3, $X^\ell_n$ for the cumulative intensity at the end of the last stage and $Y_n=N(X^\ell_n)$ for the total (uncapped) demand. Then the expected revenue satisfies
--
--   $$
--   J^\pi_n\ge r(p^D)\,nT-n\big[r(p^D)-r(p_1)\big]\Delta^{(1)}-n\sum_{i=2}^{\ell}\Big(r(p^D)-\mathbb E\big[r(\hat p_i)\big]\Big)\Delta^{(i)}-\overline p\,\mathbb E\big[(Y_n-\lfloor nx\rfloor)^+\big].
--   $$
--
--   The bound separates the loss of Algorithm 3 into a first-stage exploration loss, per-stage estimation losses and an overflow loss.
--
--   **Formalization Note** The paper writes $(Y_n-nx)^+$; with an inventory of $\lfloor nx\rfloor$ units the overflow term is $(Y_n-\lfloor nx\rfloor)^+$, which equals the paper's when $nx$ is an integer. The paper derives the bound in the case $\lambda(\overline p;\theta^*)\le x/T$, but its derivation does not use the case, so the statement carries no case hypothesis. It is stated for an arbitrary stage schedule summing to $T$; the proof uses it for the tuning (19)–(20). Expectations are lower Lebesgue integrals of nonnegative quantities, converted to real numbers.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), pp. 34-35 (PDF pp. 36-37), proof of Proposition 5, eq. (A-27)

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning
import Definitions.Def_BesbesZeevi_SingleParam_Algorithm

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- (A-27) (Besbes–Zeevi 2009, proof of Proposition 5, p. 35): for Algorithm 3 with `ℓ` stages
of positive lengths summing to `T`, with `r(p) = p λ(p; θ*)`, `p^D = p^D(θ*)` and
`Y_n = N(X^ℓ_n)`,
`J^π_n ≥ r(p^D) n T - n [r(p^D) - r(p̂_1)] Δ^{(1)} - n ∑_{i=2}^{ℓ} (r(p^D) - E r(p̂_i)) Δ^{(i)}
  - p̄ E[(Y_n - ⌊nx⌋)^+]`. -/
theorem revenue_lower_bound_A27 (D : Market) (F : Family D) (σ : Selection D F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : PoissonProcess Ω P) (n ℓ : ℕ) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (Δ : ℕ → ℝ)
    (hΔ : ∀ i ∈ Finset.Icc 1 ℓ, 0 < Δ i) (hsum : ∑ i ∈ Finset.Icc 1 ℓ, Δ i = D.T)
    (θ : ℝ) (hθ : θ ∈ F.Θ) :
    σ.pD θ * F.lam (σ.pD θ) θ * n * D.T
      - n * (σ.pD θ * F.lam (σ.pD θ) θ - F.p1 * F.lam F.p1 θ) * Δ 1
      - n * ∑ i ∈ Finset.Icc 2 ℓ,
          (σ.pD θ * F.lam (σ.pD θ) θ
            - (∫⁻ ω, ENNReal.ofReal
                (stagePrice D F σ n Δ θ (fun t => N.N t ω) i *
                  F.lam (stagePrice D F σ n Δ θ (fun t => N.N t ω) i) θ) ∂P).toReal) * Δ i
      - D.pHi * (∫⁻ ω, ENNReal.ofReal
          ((N.N (cumIntensity D F σ n Δ θ (fun t => N.N t ω) ℓ) ω : ℝ)
            - (capacity D n : ℝ)) ∂P).toReal
      ≤ expRevenue N D F σ n ℓ Δ θ := by sorry

end BesbesZeevi.SingleParam
