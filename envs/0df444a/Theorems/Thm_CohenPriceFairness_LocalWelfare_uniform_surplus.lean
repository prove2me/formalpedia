-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_surplus
-- name    : CohenPriceFairness.LocalWelfare.uniform_surplus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:36.177989+00:00
-- url     : https://prove2.me/theorems/ff2a2d57-2929-4f85-b92f-d130fb23d93f
-- title:
--   Consumer surplus under uniform valuations
-- statement:
--   Let $V$ be uniformly distributed on $[0,b]$ with $b>0$. For $0\le p\le b$,
--   $$\mathbb E\big[(V-p)^+\big]=\frac{(b-p)^2}{2b}.$$
--
--   This is the normalised consumer surplus of the linear demand model (§3, p. 8). It is one of the building blocks of the proof of Theorem 2 (p. 7; proof in Online Appendix A, p. 33).
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; normalised consumer surplus under linear demand, §3, p. 8; Online Appendix, Table 2.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

theorem uniform_surplus {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) (hpb : p ≤ b) :
    ∫ v, max (v - p) 0 ∂(uniformLaw b) = (b - p) ^ 2 / (2 * b) := by sorry

end CohenPriceFairness.LocalWelfare
