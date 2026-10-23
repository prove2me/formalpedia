-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_7
-- name    : EndogBudgetAds.Equilibrium.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:10.964584+00:00
-- url     : https://prove2.me/theorems/92d81887-c2c2-4323-9f02-b113a17ae99e
-- title:
--   Lemma 7, p. 42 — P(E_j(σ_j)) ≥ 1 − 1/m^{6ϑ−1} for every strategy σ_j
-- statement:
--   There is a universal constant $C > 0$ with the following property. Under the standing assumptions, let
--   $$m \ge \max\{(2\vartheta)^\vartheta, \exp(3\vartheta+1)\}, \qquad n \ge 6\vartheta m^{2(\vartheta+1/\vartheta)} \log(m)/C.$$
--   Then for every bidder $j$ and every admissible strategy $\sigma_j$,
--   $$\mathbb P\big(E_j(\sigma_j)\big) \ge 1 - \frac{1}{m^{6\vartheta-1}}.$$
--
--   The event $E_j(\sigma_j)$, on which no deviation is profitable, is thus typical in large markets, uniformly over the deviation.
--
--   **Formalization Note** The constant $C$ is quantified before the market, so it does not depend on $m$, $n$, $\theta_{\min}$, $\theta_{\max}$ or the rates (the paper: "a universal constant independent of $m$"; its proof takes $C = 6c/7$ with $c$ the absolute constant of Lemma 9). Powers with real exponents are `Real.rpow`.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 42, Lemma 7

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 7, p. 42: there is a universal constant `C > 0` such that, for `m ≥ max{(2ϑ)^ϑ, exp(3ϑ+1)}`
and `n ≥ 6ϑ m^{2(ϑ+1/ϑ)} log(m)/C`, the event `E_j(σ_j)` of (9) has probability at least
`1 − 1/m^{6ϑ−1}` for every bidder `j` and every admissible strategy `σ_j`. -/
theorem lemma_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Market, M.Standing →
      (2 * vt M) ^ vt M ≤ (M.m : ℝ) →
      Real.exp (3 * vt M + 1) ≤ (M.m : ℝ) →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C ≤ (M.n : ℝ) →
      ∀ (j : Fin M.m) (σj : Strategy M.n), σj.Admissible →
        1 - 1 / (M.m : ℝ) ^ (6 * vt M - 1) ≤ (valLaw M).real (EventJ M j σj) := by sorry

end EndogBudgetAds.Equilibrium
