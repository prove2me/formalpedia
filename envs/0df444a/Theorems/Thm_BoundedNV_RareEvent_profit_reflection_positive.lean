-- Prove2me | Theorems.Thm_BoundedNV_RareEvent_profit_reflection_positive
-- name    : BoundedNV.RareEvent.profit_reflection_positive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T20:02:21.935455+00:00
-- url     : https://prove2.me/theorems/f77915ff-55c1-4956-bc34-3ed0069c8b6d
-- title:
--   Proof of Proposition 4, p. 587 — decreasing density favors the upper reflected order
-- statement:
--   Let demand have density $f$ supported on $[a,b]$, with $0\le a<b$, and let $m=(a+b)/2$. Suppose $p>0$, $c=p(1-F(m))$, and $f$ is strictly decreasing on $[a,b]$. Then, for every $0<y\le(b-a)/2$,
--
--   $$
--   \pi(m+y)>\pi(m-y).
--   $$
--
--   This is the strict profit comparison in equation (50), which drives the logit choice density toward the less likely high-demand end.
--
--   **Formalization Note** The paper says “decreasing”; strict decrease is required for its displayed strict inequality. A constant density with the optimum at the midpoint gives equality.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 587 (PDF 22), proof of Proposition 4, eq. (50)

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit

namespace BoundedNV.RareEvent

/-- The strict inequality in (50), p. 587. -/
theorem profit_reflection_positive (f : ℝ → ℝ) (p c a b y : ℝ)
    (hf : BoundedNV.ExpFam.IsDemandDensity f) (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ x ∉ Set.Icc a b, f x = 0)
    (hp : 0 < p) (hy : 0 < y) (hyr : y ≤ (b - a) / 2)
    (hfractile : c = p * (1 - BoundedNV.Uniform.demandCDF f ((a + b) / 2)))
    (hanti : StrictAntiOn f (Set.Icc a b)) :
    BoundedNV.Uniform.nvProfit f p c ((a + b) / 2 - y) <
      BoundedNV.Uniform.nvProfit f p c ((a + b) / 2 + y) := by sorry

end BoundedNV.RareEvent
