-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_demand
-- name    : CohenPriceFairness.LocalWelfare.uniform_demand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:55.931018+00:00
-- url     : https://prove2.me/theorems/6f5a0651-312a-4a8a-9384-6203b918851d
-- title:
--   Purchase probability under uniform valuations
-- statement:
--   Let $V$ be uniformly distributed on $[0,b]$ with $b>0$. For every price $p\ge0$,
--   $$\Pr(V\ge p)=\max\Big\{0,\,1-\frac pb\Big\}.$$
--
--   This is the linear demand model of §3 (p. 7) and Table 2 of the Online Appendix, derived from the measure-theoretic definition of the uniform law. It is one of the building blocks of the proof of Theorem 2 (p. 7; proof in Online Appendix A, p. 33).
--
--   **Formalization Note.** The uniform law is $b^{-1}$ times Lebesgue measure restricted to $[0,b]$.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; linear demand model, §3, p. 7; Online Appendix, Table 2.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

theorem uniform_demand {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    ((uniformLaw b) (Set.Ici p)).toReal = max 0 (1 - p / b) := by sorry

end CohenPriceFairness.LocalWelfare
