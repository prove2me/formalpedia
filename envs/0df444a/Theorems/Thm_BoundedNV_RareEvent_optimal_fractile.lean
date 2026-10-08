-- Prove2me | Theorems.Thm_BoundedNV_RareEvent_optimal_fractile
-- name    : BoundedNV.RareEvent.optimal_fractile
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T20:02:07.829066+00:00
-- url     : https://prove2.me/theorems/362bdeb9-1529-4884-9672-e1858b679b5a
-- title:
--   Proof of Proposition 4, p. 586 — midpoint optimality gives the critical fractile
-- statement:
--   Let $f$ be a density of nonnegative demand, $F$ its distribution function, and $\pi(x)=p\mathbb E[\min(D,x)]-cx$ the expected profit, with $p>0$. If $m$ maximizes $\pi$ over all real order quantities, then
--
--   $$
--   c=p\bigl(1-F(m)\bigr).
--   $$
--
--   This identifies the price-cost relation at the midpoint used in the reflection calculation of Proposition 4.
--
--   **Formalization Note** A maximizer is stated directly with `IsMaxOn`; the critical-fractile relation is the conclusion, not an assumed property of a free variable. The density hypothesis includes integrability and total mass one.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 586 (PDF 21), proof of Proposition 4, paragraph before eq. (43)

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit

namespace BoundedNV.RareEvent

/-- The first step in the proof of Proposition 4, p. 586. -/
theorem optimal_fractile (f : ℝ → ℝ) (p c m : ℝ)
    (hf : BoundedNV.ExpFam.IsDemandDensity f) (hp : 0 < p)
    (hm : IsMaxOn (BoundedNV.Uniform.nvProfit f p c) Set.univ m) :
    c = p * (1 - BoundedNV.Uniform.demandCDF f m) := by sorry

end BoundedNV.RareEvent
