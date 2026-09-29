-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_expectation_minimalPenalty_eq
-- name    : CondConvexRisk.Representation.expectation_minimalPenalty_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:57:36.753656+00:00
-- url     : https://prove2.me/theorems/341e4972-9034-4702-98e5-76dfbc1c7a49
-- title:
--   Proof of Theorem 3.2 — $E_P[\alpha^*(Q)]=\alpha^*_0(Q)$ for $Q\in\mathcal P_{\mathcal G}$
-- statement:
--   Let $\rho:L^\infty\to L^\infty_{\mathcal G}$ be a conditional convex risk measure, $\rho_0(X)=E_P[\rho(X)]$ and $Q\in\mathcal P_{\mathcal G}$. If $\alpha^*(Q)=\operatorname{ess.sup}_{X\in L^\infty}\{-E_Q(X\mid\mathcal G)-\rho(X)\}$, then its expectation exists and
--   $$E_P[\alpha^*(Q)]=\alpha^*_0(Q)=\sup_{X\in L^\infty}\{-E_QX-\rho_0(X)\}.$$
--
--   This links the random conditional penalty to the deterministic unconditional one.
--
--   **Formalization Note** $\alpha^*(Q)$ is any `EReal`-valued essential supremum of $B_Q$; its expectation is the extended expectation of the appendix definitions.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 7, proof of Theorem 3.2 ("Next we prove that E_P[α*(Q)] = α*_0(Q) for every Q ∈ P_G")

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable
import Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem expectation_minimalPenalty_eq {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ) (Q : PG m P)
    (Z : Ω → EReal) (hZ : IsEssSup P (penaltyFamily m P ρ Q) Z) :
    HasExpectation P Z ∧
      expectation P Z = minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Q.1 := by sorry

end CondConvexRisk.Representation
