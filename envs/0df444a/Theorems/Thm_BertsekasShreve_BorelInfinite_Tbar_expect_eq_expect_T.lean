-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_Tbar_expect_eq_expect_T
-- name    : BertsekasShreve.BorelInfinite.Tbar_expect_eq_expect_T
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:39:43.251684+00:00
-- url     : https://prove2.me/theorems/bc0a57fa-fbd1-4fbe-9285-967994b89dbe
-- title:
--   Proposition 9.7 — $\bar T(\bar J)(p)=\int T(J)\,dp$ for lower semianalytic $J$
-- statement:
--   Let (SM) $=(S,C,U,W,p,f,\alpha,g)$ be an infinite horizon stochastic optimal control model on nonempty Borel spaces (Definitions 8.1, 9.1), with optimal cost $J^*(x)=\inf_{\pi\in\Pi'}J_\pi(x)$ over all universally measurable policies, and let (DM) be the associated deterministic model on $P(S)$ (Definition 9.4) with optimal cost $\bar J^*$ and operator $\bar T(\bar J)(p)=\inf_{q\in\bar U(p)}\{\bar g(q)+\alpha\bar J[\bar f(q)]\}$. Assume one of (P) $g\ge0$ on $\Gamma$, (N) $g\le0$ on $\Gamma$, (D) $0<\alpha<1$ and $-b\le g\le b$ on $\Gamma$.
--
--   Let $J:S\to R^*$ be lower semianalytic and satisfy $J\ge0$, $J\le0$, or $-c\le J\le c$ for some $c<\infty$, according as (P), (N), or (D) is in force, and define $\bar J(p)=\int_S J(x)\,p(dx)$ for $p\in P(S)$. Then
--   $$\bar T(\bar J)(p)=\int_S T(J)(x)\,p(dx)\qquad\forall p\in P(S),$$
--   where $T(J)(x)=\inf_{u\in U(x)}\{g(x,u)+\alpha\int_S J(x')\,t(dx'\mid x,u)\}$.
--
--   This identity transports the DP operator of (DM) to that of (SM); its proof uses the $\varepsilon$-optimal selection theorem (Proposition 7.50) through Lemma 8.2.
--
--   **Formalization Note** All integrals are extended integrals with $\infty-\infty=\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 224–225, Proposition 9.7 of Chapter 9

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_BertsekasShreve_BorelInfinite_DetModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.7** (p. 224). (P)(N)(D) Let `J : S → R*` be lower semianalytic and satisfy
`J ≥ 0`, `J ≤ 0`, or `−c ≤ J ≤ c` (`c < ∞`), according as (P), (N), or (D) is in force, and let
`J̄(p) = ∫ J(x) p(dx)`. Then `T̄(J̄)(p) = ∫ T(J)(x) p(dx)` for every `p ∈ P(S)`. -/
theorem Tbar_expect_eq_expect_T {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (J : S → EReal) (hJ : IsLowerSemianalyticFun J)
    (hcase : (M.CaseP ∧ ∀ x, 0 ≤ J x) ∨ (M.CaseN ∧ ∀ x, J x ≤ 0) ∨
      (M.CaseD ∧ ∃ c : ℝ, ∀ x, -(c : EReal) ≤ J x ∧ J x ≤ (c : EReal)))
    (p : Measure S) [IsProbabilityMeasure p] :
    M.Tbar (fun p' => DupacovaWets.Consistency.expect p' J) p =
      DupacovaWets.Consistency.expect p (M.T J) := by sorry

end BertsekasShreve.BorelInfinite
