-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_minimalPenalty_minimal
-- name    : CondConvexRisk.Representation.minimalPenalty_minimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:58:54.805793+00:00
-- url     : https://prove2.me/theorems/8de84be9-e64c-4503-b8d6-8072d2ba3984
-- title:
--   Remark 3.3 — $\alpha^*$ is the minimal penalty; $\alpha^*(Q)=\operatorname{ess.sup}_{X\in\mathcal A_\rho}\{-E_Q(X|\mathcal G)\}$
-- statement:
--   Let $\rho:L^\infty\to L^\infty_{\mathcal G}$ be a conditional convex risk measure with minimal penalty $\alpha^*$, and let $\mathcal A_\rho=\{X\in L^\infty:\rho(X)\le0\}$ be its acceptance set. Then:
--   1. $\alpha^*(Q)\le\alpha(Q)$ $P$-a.s. for every $Q\in\mathcal P_{\mathcal G}$ and every penalty function $\alpha$ for $\rho$;
--   2. for every $Q\in\mathcal P_{\mathcal G}$
--   $$\alpha^*(Q)=\operatorname*{ess.sup}_{X\in\mathcal A_\rho}\{-E_Q(X\mid\mathcal G)\}.$$
--
--   Part 2 expresses the minimal penalty through the acceptable positions only.
--
--   **Formalization Note** The paper defines $\mathcal A_\rho$ on p. 4 as a subset of $L^\infty_{\mathcal G}$; that is a misprint (on $L^\infty_{\mathcal G}$ the set would be $\{X\ge0\}$ and part 2 would fail), and the acceptance set is taken in $L^\infty$, as in the unconditional theory the remark refers to.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 8, Remark 3.3 (acceptance set A_ρ from p. 4, read in L∞)

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem minimalPenalty_minimal {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (αstar : PG m P → Ω → ENNReal) (hstar : IsMinimalPenalty m P ρ αstar) :
    (∀ α : PG m P → Ω → ENNReal, IsPenaltyFor m P ρ α →
      ∀ Q : PG m P, αstar Q ≤ᵐ[P] α Q) ∧
    ∀ Q : PG m P,
      IsEssSup P
        (fun X : {X : Ω → ℝ // MemLp X ⊤ P ∧ ρ X ≤ᵐ[P] 0} =>
          fun ω => ((-(Q.1[X.1 | m]) ω : ℝ) : EReal))
        (fun ω => (αstar Q ω : EReal)) := by sorry

end CondConvexRisk.Representation
