-- Prove2me | Theorems.Thm_BertsekasShreve_AnalyticSelection_analytic_universallyMeasurable
-- name    : BertsekasShreve.AnalyticSelection.analytic_universallyMeasurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T00:50:44.801981+00:00
-- url     : https://prove2.me/theorems/1f43e1d4-cf00-45f7-a9c8-87e0c2059555
-- title:
--   Corollary 7.42.1 — every analytic set is universally measurable
-- statement:
--   Let $X$ be a Borel space. Every analytic set $A\subseteq X$ is universally measurable: for every probability measure $p$ on $(X,\mathscr B_X)$, $A$ belongs to the $p$-completion $\mathscr B_X(p)$ of the Borel σ-algebra, that is,
--   $$A\in\mathscr U_X=\bigcap_{p\in P(X)}\mathscr B_X(p).$$
--
--   Consequently $\mathscr A_X\subseteq\mathscr U_X$, which is what allows analytically measurable policies and lower semianalytic costs to be integrated against arbitrary probability measures.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 169, Corollary 7.42.1

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

open MeasureTheory

namespace BertsekasShreve.AnalyticSelection

/-- **Corollary 7.42.1** (p. 169). In a Borel space every analytic set is universally
measurable. -/
theorem analytic_universallyMeasurable {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    (A : Set X) (hA : AnalyticSet A) : IsUniversallyMeasurable A := by sorry

end BertsekasShreve.AnalyticSelection
