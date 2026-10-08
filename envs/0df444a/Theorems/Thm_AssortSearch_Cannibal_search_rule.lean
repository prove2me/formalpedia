-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_search_rule
-- name    : AssortSearch.Cannibal.search_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:49.402747+00:00
-- url     : https://prove2.me/theorems/8ff4d48b-e5db-448f-ab96-273a1dbeea72
-- title:
--   Search is worthwhile at $y=U_{\max}$ if and only if $u_r-b\ge y$
-- statement:
--   Let $\mu>0$ and let the search shock $\zeta_r$ have the zero-mean Gumbel law with scale $\mu$ and density $f$. A consumer who searches pays $b$ and receives $U_r=u_r+\zeta_r$. For every realised maximum utility $y=U_{\max}$,
--   $$
--   \int_{y-u_r}^{\infty}(u_r+x-y)f(x)\,dx-\int_{-\infty}^{y-u_r}(y-u_r-x)f(x)\,dx\ \ge\ b
--   \quad\Longleftrightarrow\quad u_r-b\ \ge\ y .
--   $$
--   The first term is the expected gain from search and the second the expected loss. The equivalence identifies the search threshold $\bar U=u_r-b$: a consumer in the independent assortment model buys only when $U_{\max}$ exceeds $\bar U$. The paper states it in the proof of Theorem 1, "after rearranging terms, and recognizing $E[\zeta_r]=0$".
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 8 (PDF 10), proof of Theorem 1

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- The search rule (proof of Theorem 1, p. 8): at a realised maximum utility `y`, search is
worthwhile if and only if `u_r - b ≥ y`, i.e. `y ≤ Ū`. -/
theorem search_rule (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (ur b y : ℝ) :
    SearchWorthwhile G ur b y ↔ y ≤ searchThreshold ur b := by sorry

end AssortSearch.Cannibal
