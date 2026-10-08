-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_change_of_variables
-- name    : AssortSearch.Cannibal.change_of_variables
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:39.363952+00:00
-- url     : https://prove2.me/theorems/325d1473-a974-4803-9dbc-f0482c8b5df5
-- title:
--   Change of variables $\delta=\exp[-(\phi/\mu+\gamma)]$: the demand integral equals $\int_0^\alpha\exp[-\delta(v_0+\sum_{j\in S}v_j)/v_i]\,d\delta$
-- statement:
--   Let $\mu>0$, $F$ and $f$ the zero-mean Gumbel distribution function and density with scale $\mu$, $\bar U=u_r-b$, $v_j=\exp((u_j-p_j)/\mu)$, $v_0=\exp(u_0/\mu)$ and $i\in S$. Then
--   $$
--   \int_{\bar U-(u_i-p_i)}^{\infty} f(\phi)\prod_{j\in\{0\}\cup (S\setminus\{i\})}F\big((u_i-p_i)+\phi-(u_j-p_j)\big)\,d\phi
--   =\int_0^{\alpha}\exp\Big[-\delta\,\frac{v_0+\sum_{j\in S}v_j}{v_i}\Big]\,d\delta,
--   $$
--   where $\alpha=\exp\big[-\big((\bar U-(u_i-p_i))/\mu+\gamma\big)\big]=v_i\,e^{-(\bar U/\mu+\gamma)}$. It is the substitution $\delta=\exp[-(\phi/\mu+\gamma)]$ that the paper makes, "following the process of deriving choice probabilities in the traditional MNL".
--
--   **Formalization Note** The paper prints $\alpha=\exp[-((\bar U-u_i)/\mu+\gamma)]$, with $u_i$ where the substitution gives $u_i-p_i$; the two agree when $p_i=0$. The corrected $\alpha$ is stated, because only it makes the next display of the paper (Theorem 1) follow. The statement is pure calculus and involves no probability measure.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 9 (PDF 11), proof of Theorem 1

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- The change of variables `δ = exp[-(φ/μ + γ)]` (proof of Theorem 1, p. 9):
`∫_{Ū-(u_i-p_i)}^∞ f(φ) ∏_{j=0, j∈S∖{i}} F((u_i-p_i)+φ-(u_j-p_j)) dφ
  = ∫_0^α exp[-δ (v_0 + ∑_{j∈S} v_j)/v_i] dδ` with `α = exp[-((Ū - (u_i-p_i))/μ + γ)]`
(the printed `α` has `u_i` for `u_i - p_i`). -/
theorem change_of_variables {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (ur b : ℝ) (w : Fin n → ℝ) (u0 : ℝ)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    (∫ φ in Set.Ioi (searchThreshold ur b - w i),
        gumbelPdf μ φ * ∏ j ∈ (Finset.insertNone S).erase (some i),
          gumbelCdf μ (w i + φ - netUtility w u0 j)) =
      ∫ δ in (0 : ℝ)..Real.exp (-((searchThreshold ur b - w i) / μ +
          Real.eulerMascheroniConstant)),
        Real.exp (-(δ * ((pref0 μ u0 + ∑ j ∈ S, pref μ w j) / pref μ w i))) := by sorry

end AssortSearch.Cannibal
