-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_nonbuyer
-- name    : CohenPriceFairness.LocalWelfare.uniform_nonbuyer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:32.788686+00:00
-- url     : https://prove2.me/theorems/aa608692-07e9-410e-9603-e42a23aa0b5a
-- title:
--   No-purchase valuation under uniform valuations
-- statement:
--   Let $V$ be uniformly distributed on $[0,b]$ with $b>0$. For $0<p\le b$, the event $\{V<p\}$ has positive probability and
--   $$\mathbb E[V\mid V<p]=\frac p2.$$
--
--   This is the no-purchase valuation $N_i(p)=\min\{b_i,p\}/2$ of the linear demand model (§3, p. 8) on the active price range. It is one of the building blocks of the proof of Theorem 2 (p. 7; proof in Online Appendix A, p. 33).
--
--   **Formalization Note.** The conditional mean is written as $\int_{\{v<p\}}v\,d\mu/\mu(\{v<p\})$, with value $0$ when $\mu(\{v<p\})=0$.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; no-purchase valuation under linear demand, §3, p. 8; Online Appendix, Table 2.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

theorem uniform_nonbuyer {b p : ℝ} (hb : 0 < b) (hp : 0 < p) (hpb : p ≤ b) :
    (if (uniformLaw b) (Set.Iio p) = 0 then 0
      else (∫ v in Set.Iio p, v ∂(uniformLaw b)) / ((uniformLaw b) (Set.Iio p)).toReal) = p / 2 := by
  sorry

end CohenPriceFairness.LocalWelfare
