-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_zero_mean
-- name    : AssortSearch.Cannibal.zero_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:47.378039+00:00
-- url     : https://prove2.me/theorems/4496169b-f462-4b8e-bc17-5fc702320e45
-- title:
--   The zero-mean Gumbel law with scale $\mu$ has mean $0$ ($E[\zeta_r]=0$)
-- statement:
--   Let $\mu>0$ and let $G$ be the law with distribution function $F(x)=\exp[-\exp(-(x/\mu+\gamma))]$, where $\gamma$ is Euler's constant. Then a random variable $\zeta$ with law $G$ is integrable and
--   $$
--   E[\zeta]=\int_{\mathbb R}x\,dG(x)=0 .
--   $$
--   The paper calls this law "zero mean" (p. 5) and uses $E[\zeta_r]=0$ for the search shock to simplify the search decision in the proof of Theorem 1 (p. 8). The constant $\gamma$ in $F$ is exactly what centres the Gumbel law.
--
--   **Formalization Note** Integrability is part of the conclusion, since Lean's integral of a non-integrable function is $0$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 8 (PDF 10), proof of Theorem 1 ("recognizing E[ζ_r] = 0"); p. 5 (PDF 7), the zero-mean Gumbel law

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- The search shock has mean zero (p. 8, "recognizing E[ζ_r] = 0"; the law is called
"zero mean" on p. 5): a random variable with the zero-mean Gumbel law of scale `μ` is integrable
and has expectation `0`. -/
theorem zero_mean (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) :
    Integrable (fun x : ℝ => x) G ∧ ∫ x, x ∂G = 0 := by sorry

end AssortSearch.Cannibal
