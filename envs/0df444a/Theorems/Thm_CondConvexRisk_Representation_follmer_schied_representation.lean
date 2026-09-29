-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_follmer_schied_representation
-- name    : CondConvexRisk.Representation.follmer_schied_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:56:03.147904+00:00
-- url     : https://prove2.me/theorems/56f43b41-f247-4a84-81ae-21b56658e8b2
-- title:
--   Föllmer–Schied Theorem 4.26 as used on p. 7 — robust representation of a convex risk measure continuous from above
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\rho_0:L^\infty\to\mathbb R$ a convex risk measure (monotone, cash invariant, convex) that is continuous from above. Then for every $X\in L^\infty$
--   $$\rho_0(X)=\sup_{Q\in\mathcal P}\{-E_Q X-\alpha^*_0(Q)\},\qquad \alpha^*_0(Q)=\sup_{X\in L^\infty}\{-E_Q X-\rho_0(X)\},$$
--   where $\mathcal P$ is the set of probability measures $Q\ll P$ on $\mathcal F$.
--
--   This unconditional representation theorem is applied in the paper to $\rho_0(X)=E_P[\rho(X)]$ and is the functional-analytic core of Theorem 3.2.
--
--   **Formalization Note** The supremum is taken in `EReal`; $\alpha^*_0(Q)$ may be $+\infty$, in which case the term is $-\infty$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 7 (proof of Theorem 3.2); [8] Föllmer–Schied, Stochastic Finance (2002), Theorem 4.26

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem follmer_schied_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ρ₀ : (Ω → ℝ) → ℝ) (hρ₀ : IsConvexRiskMeasure P ρ₀)
    (hcont : IsContinuousFromAbove₀ P ρ₀) (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    (ρ₀ X : EReal) =
      ⨆ Q : {Q : Measure Ω // IsProbabilityMeasure Q ∧ Q ≪ P},
        ((-(∫ ω, X ω ∂Q.1) : ℝ) : EReal) - minPenalty₀ P ρ₀ Q.1 := by sorry

end CondConvexRisk.Representation
