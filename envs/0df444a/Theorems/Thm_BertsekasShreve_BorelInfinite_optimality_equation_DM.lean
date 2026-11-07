-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_optimality_equation_DM
-- name    : BertsekasShreve.BorelInfinite.optimality_equation_DM
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T05:39:46.249408+00:00
-- url     : https://prove2.me/theorems/5ed1676d-4cfe-441c-b1a2-527ad3410f63
-- title:
--   Proposition 9.8, Eq. (21) — the (DM) optimality equation $\bar J^*=\bar T(\bar J^*)$
-- statement:
--   Let (SM) $=(S,C,U,W,p,f,\alpha,g)$ be an infinite horizon stochastic optimal control model on nonempty Borel spaces (Definitions 8.1, 9.1), with optimal cost $J^*(x)=\inf_{\pi\in\Pi'}J_\pi(x)$ over all universally measurable policies, and let (DM) be the associated deterministic model on $P(S)$ (Definition 9.4) with optimal cost $\bar J^*$ and operator $\bar T(\bar J)(p)=\inf_{q\in\bar U(p)}\{\bar g(q)+\alpha\bar J[\bar f(q)]\}$. Assume one of (P) $g\ge0$ on $\Gamma$, (N) $g\le0$ on $\Gamma$, (D) $0<\alpha<1$ and $-b\le g\le b$ on $\Gamma$.
--
--   Then the optimal cost of (DM) satisfies the optimality equation
--   $$\bar J^*(p)=\bar T(\bar J^*)(p)\qquad\forall p\in P(S).$$
--
--   The book obtains this from the abstract monotone-mapping theory (Propositions 4.2(a), 5.2, 5.3), since (DM) is a deterministic model with no measurability restrictions on policies; combined with Propositions 9.5 and 9.7 it yields the optimality equation $J^*=T(J^*)$ for (SM) (Eq. (22)).
--
--   **Formalization Note** The equation is stated at probability measures $p$, the states of (DM).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 225, Proposition 9.8, Eq. (21) of Chapter 9

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_BertsekasShreve_BorelInfinite_DetModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.8**, Eq. (21) (p. 225). (P)(N)(D) The optimal cost of (DM) satisfies the
optimality equation `J̄* = T̄(J̄*)` on `P(S)`. -/
theorem optimality_equation_DM {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) (p : Measure S) [IsProbabilityMeasure p] :
    M.Jbarstar p = M.Tbar M.Jbarstar p := by sorry

end BertsekasShreve.BorelInfinite
