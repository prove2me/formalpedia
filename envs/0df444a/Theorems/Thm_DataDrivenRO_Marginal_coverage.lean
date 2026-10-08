-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_coverage
-- name    : DataDrivenRO.Marginal.coverage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:21:38.533306+00:00
-- url     : https://prove2.me/theorems/f661e327-87dd-4eed-b249-b46d445f09b7
-- title:
--   p. 21 — union bound: ℙ* ∈ 𝒫^M with probability at least 1 − α
-- statement:
--   Under the standing assumptions ($d\ge1$, $0<\epsilon<1$, $0<\alpha<1$, $\mathbb P^*$ a probability measure on $\mathbb R^d$ supported in the known box $[\hat{\mathbf u}^{(0)},\hat{\mathbf u}^{(N+1)}]$, and data with an admissible law $Q$: the data are $N$ samples of each marginal, $\hat u^1_i,\dots,\hat u^N_i$ i.i.d. from $\mathbb P^*_i$ for each $i$, with arbitrary (unknown) dependence between the samples of different marginals),
--   $$\mathbb P^*_{\mathcal S}\big(\mathbb P^*\in\mathcal P^M\big)\ge1-\alpha ,$$
--   where $\mathcal P^M$ is the confidence region of §6: the probability measures on the box with $\mathrm{VaR}_{\epsilon/d}(\mathbf e_i)\le\hat u^{(s)}_i$ and $\mathrm{VaR}_{\epsilon/d}(-\mathbf e_i)\le-\hat u^{(N-s+1)}_i$ for every $i$.
--
--   This is the statement that the multivariate test of §6 is valid at level $\alpha$, i.e. Step 1 of the paper's schema for this confidence region.
--
--   **Formalization Note** The sampling law `Q` is any law with `IsMarginalSampleLaw Pstar Q`; the event depends jointly on all coordinates, so the bound is claimed for every coupling of the marginal samples, as the paper's model requires. The probability of the (possibly non-measurable) event is the outer measure, which is what "with probability at least" means for a lower bound. The second condition of $\mathcal P^M$ is the corrected lower-tail condition; see the definitions item.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §6, multivariate hypothesis H₀ and 𝒫^M, p. 21

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- p. 21, union bound: with probability at least `1 − α` over the sample, `ℙ*` lies in the
confidence region `𝒫^M`. -/
theorem coverage {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (Q : Measure (Fin N → Fin d → ℝ)) (hQ : IsMarginalSampleLaw Pstar Q) (lo hi : Fin d → ℝ)
    (hsupp : Pstar (box lo hi)ᶜ = 0) :
    ENNReal.ofReal (1 - α) ≤
      Q {S | Pstar ∈ PM S lo hi ε α} := by sorry

end DataDrivenRO.Marginal
