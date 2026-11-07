-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_Jbarstar_eq_expect_Jstar
-- name    : BertsekasShreve.BorelInfinite.Jbarstar_eq_expect_Jstar
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:39:48.45271+00:00
-- url     : https://prove2.me/theorems/ed07fb87-d1a1-4db7-af10-3c85d719fd2a
-- title:
--   Proposition 9.5 — $\bar J^*(p)=\int J^*\,dp$ under (P), (N), (D)
-- statement:
--   Let (SM) $=(S,C,U,W,p,f,\alpha,g)$ be an infinite horizon stochastic optimal control model on nonempty Borel spaces (Definitions 8.1, 9.1), with optimal cost $J^*(x)=\inf_{\pi\in\Pi'}J_\pi(x)$ over all universally measurable policies, and let (DM) be the associated deterministic model on $P(S)$ (Definition 9.4) with optimal cost $\bar J^*$ and operator $\bar T(\bar J)(p)=\inf_{q\in\bar U(p)}\{\bar g(q)+\alpha\bar J[\bar f(q)]\}$. Assume one of (P) $g\ge0$ on $\Gamma$, (N) $g\le0$ on $\Gamma$, (D) $0<\alpha<1$ and $-b\le g\le b$ on $\Gamma$.
--
--   Then for every $p\in P(S)$,
--   $$\bar J^*(p)=\int_S J^*(x)\,p(dx).$$
--
--   This is one of the two key relationships between (SM) and (DM): the optimal cost of the deterministic model is the average of the stochastic optimal cost.
--
--   **Formalization Note** The integral is the extended integral $\int (J^*)^+dp-\int (J^*)^-dp$ with $\infty-\infty=\infty$ (`DupacovaWets.Consistency.expect`).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 223, Proposition 9.5 of Chapter 9

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_BertsekasShreve_BorelInfinite_DetModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.5** (p. 223). (P)(N)(D) For every `p ∈ P(S)`, `J̄*(p) = ∫ J*(x) p(dx)`. -/
theorem Jbarstar_eq_expect_Jstar {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) (p : Measure S) [IsProbabilityMeasure p] :
    M.Jbarstar p = DupacovaWets.Consistency.expect p M.Jstar := by sorry

end BertsekasShreve.BorelInfinite
