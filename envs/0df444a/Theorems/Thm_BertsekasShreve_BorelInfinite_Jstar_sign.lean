-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_Jstar_sign
-- name    : BertsekasShreve.BorelInfinite.Jstar_sign
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T05:39:44.248539+00:00
-- url     : https://prove2.me/theorems/f68518e8-c969-416d-aef3-5e2e763dad80
-- title:
--   Sign and boundedness of $J^*$ under (P), (N), (D)
-- statement:
--   Let (SM) $=(S,C,U,W,p,f,\alpha,g)$ be an infinite horizon stochastic optimal control model on nonempty Borel spaces (Definitions 8.1, 9.1), with costs $J_\pi(x)=\sum_{k=0}^\infty\alpha^k\int g\,dq_k(\pi,p_x)$ (Eq. (1)) and optimal cost $J^*(x)=\inf_{\pi\in\Pi'}J_\pi(x)$ (Eq. (2)). Then
--
--   1. under (P) ($g\ge0$ on $\Gamma$): $J^*(x)\ge0$ for all $x$;
--   2. under (N) ($g\le0$ on $\Gamma$): $J^*(x)\le0$ for all $x$;
--   3. under (D) ($0<\alpha<1$, $-b\le g\le b$ on $\Gamma$): there is $c\in\mathbb R$ with $-c\le J^*(x)\le c$ for all $x$.
--
--   These are the sign conditions that allow Proposition 9.7 to be applied with $J=J^*$ in the proof of Proposition 9.8 (p. 226).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 214–215, Definitions 9.2–9.3 and Eqs. (1)–(2) of Chapter 9, as used in the proof of Proposition 9.8 (p. 226)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_BertsekasShreve_BorelInfinite_DetModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- Section 9.1, Definition 9.3 and Eq. (2) (pp. 214–215), as used in the proof of
Proposition 9.8 (p. 226): `J* ≥ 0` under (P), `J* ≤ 0` under (N), and `J*` is bounded under (D). -/
theorem Jstar_sign {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W) :
    (M.CaseP → ∀ x, 0 ≤ M.Jstar x) ∧ (M.CaseN → ∀ x, M.Jstar x ≤ 0) ∧
      (M.CaseD → ∃ c : ℝ, ∀ x, -(c : EReal) ≤ M.Jstar x ∧ M.Jstar x ≤ (c : EReal)) := by sorry

end BertsekasShreve.BorelInfinite
