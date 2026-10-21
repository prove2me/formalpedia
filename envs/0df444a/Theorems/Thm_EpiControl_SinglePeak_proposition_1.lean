-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_proposition_1
-- name    : EpiControl.SinglePeak.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:29.789134+00:00
-- url     : https://prove2.me/theorems/fdf7efea-afd8-4459-8638-f3ed2b728ae7
-- title:
--   Proposition 1, p. 6 (PDF 7) — an optimal policy exists and admits a positive costate η∗ satisfying (5)–(6)
-- statement:
--   Under the standing assumptions of §2, an optimal policy exists. Moreover, for every optimal policy $\beta^*$ with SIR path $(s^*,i^*)$ there is a function $\eta^*:[0,T]\to\mathbb R$ with $\eta^*(T)=\frac{v(i^*(T))}{\gamma i^*(T)}$ such that for almost every $t\in[0,T]$
--   $$(\eta^*)'(t)=\eta^*(t)\beta^*(t)i^*(t)-v'(i^*(t))+\frac{v(i^*(t))+c(\beta^*(t))-\min_{b\in B}\big[\tfrac1\gamma v(i^*(T))s^*(T)b+c(b)\big]}{i^*(t)}, \tag{5}$$
--   $$\beta^*(t)\in\arg\min_{b\in B}\big[\eta^*(t)i^*(t)s^*(t)b+c(b)\big], \tag{6}$$
--   and $\eta^*(t)>0$ for all $t\in[0,T]$.
--
--   The optimal control depends on the state and the multipliers only through the gain $g^*=\eta^*i^*s^*$, which drives everything that follows.
--
--   **Formalization Note** "There is such an $\eta^*$" is the predicate `IsCostate`: $\eta$ continuous on $[0,T]$, the terminal value, (5) in integral form (so $\eta$ is absolutely continuous), (6) almost everywhere on $[0,T]$, and $\eta>0$ on $[0,T]$. The minimum in (5) is $M(v(i(T))s(T)/\gamma)$.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 6 (PDF 7), Proposition 1

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem proposition_1 (P : Params) (hP : P.Standing) :
    (∃ β s i : ℝ → ℝ, P.IsOptimal β s i) ∧
    ∀ β s i : ℝ → ℝ, P.IsOptimal β s i → ∃ η : ℝ → ℝ, P.IsCostate β s i η := by sorry
end EpiControl.SinglePeak
