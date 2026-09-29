-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_jh_strictMonoOn
-- name    : CachonPushPull.Pareto.jh_strictMonoOn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:27:22.174604+00:00
-- url     : https://prove2.me/theorems/c0360d55-a5fc-4929-bdde-6a5a5a78384d
-- title:
--   Lemma 1: $j(q)h(q)$ is increasing for $q > 0$
-- statement:
--   Let demand satisfy the standing assumptions, including the IGFR property. With $j(q) = S(q)/(1 - F(q))$, $S(q) = q - \int_0^q F(x)\,dx$, and the hazard rate $h(q) = f(q)/(1 - F(q))$, the product
--   $$
--   q \longmapsto j(q)\,h(q)
--   $$
--   is strictly increasing on $(0, \infty)$.
--
--   This is the key analytic lemma of the paper: it gives the convexity of the pull supplier's profit, the concavity of the pull retailer's profit (Theorem 2), and the single crossing in Lemma 4.
--
--   **Formalization Note** The paper writes "increasing"; its proof shows a positive derivative, so the statement is strict.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Lemma 1 (proof p. 228)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Lemma 1, p. 227: for `q > 0`, `j(q) h(q)` is (strictly) increasing. -/
theorem jh_strictMonoOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) :
    StrictMonoOn (fun q : ℝ => j μ q * hazard μ f q) (Set.Ioi 0) := by sorry

end CachonPushPull.Pareto
