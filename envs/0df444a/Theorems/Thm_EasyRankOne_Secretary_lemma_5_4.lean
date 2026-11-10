-- Prove2me | Theorems.Thm_EasyRankOne_Secretary_lemma_5_4
-- name    : EasyRankOne.Secretary.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:07:28.698826+00:00
-- url     : https://prove2.me/theorems/3790defa-9eda-4392-9cda-1e888772275d
-- title:
--   Lemma 5.4 — the survivor distributions and the accepting masses (12) satisfy consistency (9)
-- statement:
--   Fix $p\in[1/e,1)$. The survivor distributions $\mathcal D_{O,t}$ (Definition 5.1, empty background) and the accepting masses (12)
--   $$z_{O,e,t}(A)=\tfrac pt\,\mathcal D_{O-e,t,e}(A)\ \ (t>p,\ e\in\mathrm{Greedy}(O)),\qquad 0 \text{ otherwise},$$
--   satisfy consistency (9): for every ordered set $O$ with $m=|O|>0$, every $A\subseteq O$ and every $0<t\le 1$,
--   $$t^m\mathcal D_{O,t}(A)=\int_0^t u^{m-1}\Big[\sum_{e\in O\setminus A}\big(\mathcal D_{O-e,u}(A)-z_{O,e,u}(A)\big)+\sum_{e\in A} z_{O,e,u}(A-e)\Big]du .$$
--
--   With Lemma 5.3 this makes the survivor family feasible (Theorem 5.2).
--
--   Differences from the source:
--   - reading: the integral in (9) → required to exist (the integrand is integrable on (0, t]) as part of `Consistency`; reason: an equation between integrals presupposes them
--   - generalization: §4's standing assumption "positive rank" → not imposed; reason: in rank 0 all survivor distributions are the point mass at ∅ and every z is 0, and both sides of (9) equal t^m·1{A = ∅}; specializes to the source
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 20, Lemma 5.4

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_Greedy
import Definitions.Def_EasyRankOne_Secretary_ContinuousTime
import Definitions.Def_EasyRankOne_Secretary_Survivor

namespace EasyRankOne.Secretary

theorem lemma_5_4 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (hE : M.E = Set.univ) (p : ℝ) (hp : p ∈ Set.Ico (Real.exp (-1)) 1) :
    Consistency (survFamily M p) (zSurv M p) := by sorry

end EasyRankOne.Secretary
