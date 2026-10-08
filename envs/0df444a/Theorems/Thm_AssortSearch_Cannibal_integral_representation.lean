-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_integral_representation
-- name    : AssortSearch.Cannibal.integral_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:34.99132+00:00
-- url     : https://prove2.me/theorems/0548010c-e544-4090-9016-69455663e78a
-- title:
--   $q_i^{si}(S)=\int_{\bar U-(u_i-p_i)}^\infty f(\phi)\prod_{j\in\{0\}\cup S\setminus\{i\}}F((u_i-p_i)+\phi-(u_j-p_j))\,d\phi$
-- statement:
--   Let $\mu>0$, let all shocks be i.i.d. zero-mean Gumbel with scale $\mu$, distribution function $F$ and density $f$, and let $\bar U=u_r-b$. For $i\in S$, write $u_0-p_0=u_0$. The independent-assortment demand of variant $i$ is
--   $$
--   q_i^{si}(S)=\int_{\bar U-(u_i-p_i)}^{\infty} f(\phi)\prod_{j\in\{0\}\cup (S\setminus\{i\})}F\big((u_i-p_i)+\phi-(u_j-p_j)\big)\,d\phi .
--   $$
--   Here $\phi$ is the realisation of $\zeta_i$: variant $i$ is bought when $U_i$ exceeds the search threshold $\bar U$, the no-purchase utility and every other variant's utility. This is the integral the paper then evaluates in closed form (Theorem 1).
--
--   **Formalization Note** The paper writes the product index as "$j=0,\ j\in S/i$", meaning $j\in\{0\}\cup(S\setminus\{i\})$. The demand on the left is the probability of the choice event with the paper's search rule, so this identity uses the search rule.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), pp. 8–9 (PDF 10–11), proof of Theorem 1

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- The integral representation of `q_i^si(S)` (proof of Theorem 1, pp. 8–9):
`q_i^si(S) = ∫_{Ū-(u_i-p_i)}^∞ f(φ) ∏_{j=0, j∈S∖{i}} F((u_i-p_i) + φ - (u_j-p_j)) dφ`. -/
theorem integral_representation {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ)
    [IsProbabilityMeasure G] (hG : IsZeroMeanGumbel μ G) (ur b : ℝ) (w : Fin n → ℝ) (u0 : ℝ)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    searchProb G ur b w u0 S i =
      ∫ φ in Set.Ioi (searchThreshold ur b - w i),
        gumbelPdf μ φ * ∏ j ∈ (Finset.insertNone S).erase (some i),
          gumbelCdf μ (w i + φ - netUtility w u0 j) := by sorry

end AssortSearch.Cannibal
