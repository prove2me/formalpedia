-- Prove2me | Theorems.Thm_AssortSearch_FullAssort_outside_max_law
-- name    : AssortSearch.FullAssort.outside_max_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:01.452791+00:00
-- url     : https://prove2.me/theorems/29b9b8ac-7e62-49f1-8ec1-986b197f7306
-- title:
--   Proof of Theorem 3, p. 11 — $w(\bar y,S)$ is the density of $\max_{i\in\bar S} U_i$
-- statement:
--   Let the utility shocks $\zeta_1, \dots, \zeta_n$ be independent, each with the zero-mean Gumbel distribution function $F(x) = \exp[-\exp(-(x/\mu+\gamma))]$ of scale $\mu > 0$. Let variant $i$ have expected net utility $a_i = u_i - p_i$, utility $U_i = a_i + \zeta_i$ and preference $v_i = \exp(a_i/\mu)$. Let $S \subsetneq N$ be an assortment and $\bar S = N - S$. Then for every $y \in \mathbb R$
--
--   $$\Pr\Big(\max_{i \in \bar S} U_i \le y\Big) = G_S(y) = \exp\big(-e^{-(y/\mu+\gamma)}\,\bar V_S\big), \qquad \bar V_S = \sum_{i\in\bar S} v_i,$$
--
--   and $G_S$ is differentiable with derivative $G_S'(y) = w(y, S) = (\bar V_S/\mu)\, e^{-(y/\mu+\gamma)}\, G_S(y)$. So $w(\cdot, S)$ is the density of the best utility outside the assortment.
--
--   The paper asserts this without proof ("it is straightforward to evaluate $w(\bar y, S)$"). It is what links the explicit density used in the mission's definition to the consumer's search problem.
--
--   **Formalization Note** The joint law of the shocks is the product measure on $\mathbb R^n$; the event $\{\max_{i\in\bar S} U_i \le y\}$ is written as $\{\forall i \in \bar S,\ a_i + \zeta_i \le y\}$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 11 (PDF 13), proof of Theorem 3; p. 5 (PDF 7), F(x)

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

namespace AssortSearch.FullAssort

open MeasureTheory

/-- Proof of Theorem 3 (p. 11): let the shocks `ζ_1, …, ζ_n` be i.i.d. with the zero-mean Gumbel
law `G` of scale `μ`, let variant `i` have expected net utility `a i = u_i − p_i` and preference
`v_i = exp(a_i/μ)`, and let `S ⊊ N`. Then the best utility outside the assortment,
`max_{i ∈ S̄} (a_i + ζ_i)`, has distribution function `G_S` (`outsideCdf`), and `G_S` has
derivative `w(·, S)` everywhere, so `w(·, S)` is its density. -/
theorem outside_max_law {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : AssortSearch.Cannibal.IsZeroMeanGumbel μ G) (a : Fin n → ℝ) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    (∀ y : ℝ, (Measure.pi (fun _ : Fin n => G) {ζ | ∀ i ∈ Sᶜ, a i + ζ i ≤ y}).toReal =
        outsideCdf μ (fun i => Real.exp (a i / μ)) S y) ∧
      ∀ y : ℝ, HasDerivAt (outsideCdf μ (fun i => Real.exp (a i / μ)) S)
        (w μ (fun i => Real.exp (a i / μ)) S y) y := by sorry

end AssortSearch.FullAssort
