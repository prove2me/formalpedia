-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_test_valid
-- name    : DataDrivenRO.Marginal.test_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:21:12.559995+00:00
-- url     : https://prove2.me/theorems/ef10d5a8-0018-414c-8bef-df1d183e1edb
-- title:
--   pp. 20–21 — the one-sided order-statistic tests for VaR_{ε/d}(±eᵢ) are valid at level α/2d
-- statement:
--   Let $d\ge1$, $0<\epsilon<1$, $0<\alpha<1$, and let $\mathbb P^*$ be a probability measure on $\mathbb R^d$ supported in the box $[\hat{\mathbf u}^{(0)},\hat{\mathbf u}^{(N+1)}]$. Suppose the data have an admissible law $Q$: the data are $N$ samples of each marginal, $\hat u^1_i,\dots,\hat u^N_i$ i.i.d. from $\mathbb P^*_i$ for each $i$, with arbitrary (unknown) dependence between the samples of different marginals. Let $\hat u^{(j)}_i$ be the order statistics of coordinate $i$ (with the box ends at $j=0,N+1$) and let $s$ be the index of (26). Then for every coordinate $i$:
--
--   1. (upper tail) $\displaystyle \mathbb P^*_{\mathcal S}\big(\hat u^{(s)}_i<\mathrm{VaR}^{\mathbb P^*}_{\epsilon/d}(\mathbf e_i)\big)\le\frac{\alpha}{2d}$;
--   2. (lower tail) $\displaystyle \mathbb P^*_{\mathcal S}\big(-\hat u^{(N-s+1)}_i<\mathrm{VaR}^{\mathbb P^*}_{\epsilon/d}(-\mathbf e_i)\big)\le\frac{\alpha}{2d}$,
--
--   where $\mathbb P^*_{\mathcal S}$ is the law $Q$ of the sample. In words, the test that rejects $\mathrm{VaR}^{\mathbb P^*}_{\epsilon/d}(\mathbf e_i)\ge q$ when $q>\hat u^{(s)}_i$, and its mirror image with threshold $\hat u^{(N-s+1)}_i$ for $\mathrm{VaR}^{\mathbb P^*}_{\epsilon/d}(-\mathbf e_i)$, each have level $\alpha/(2d)$ (David and Nagaraja 1970, Sec. 7.1).
--
--   These two bounds, one per tail and coordinate, are the $2d$ events that the union bound of §6 combines into the confidence region $\mathcal P^M$.
--
--   **Formalization Note** The sample is `S : Fin N → Fin d → ℝ` (`S k i` is the $k$-th sample of marginal $i$) with any law `Q` satisfying `IsMarginalSampleLaw Pstar Q` (§6: marginals observed separately, dependence between them not assumed). Probabilities of events are outer measures, which is the right reading for an upper bound.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §6, (26) and the two paragraphs after it, pp. 20–21

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- pp. 20–21: the one-sided order-statistic tests for `VaR^{ℙ*}_{ε/d}(eᵢ)` (threshold `û^(s)_i`)
and for `VaR^{ℙ*}_{ε/d}(−eᵢ)` (threshold `û^(N−s+1)_i`) are each valid at level `α/(2d)`. -/
theorem test_valid {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (Q : Measure (Fin N → Fin d → ℝ)) (hQ : IsMarginalSampleLaw Pstar Q) (lo hi : Fin d → ℝ)
    (hsupp : Pstar (box lo hi)ᶜ = 0) (i : Fin d) :
    Q {S | uhat S lo hi i (sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i 1)}
      ≤ ENNReal.ofReal (α / (2 * d)) ∧
    Q {S | -uhat S lo hi i (N + 1 - sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i (-1))}
      ≤ ENNReal.ofReal (α / (2 * d)) := by sorry

end DataDrivenRO.Marginal
