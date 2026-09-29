-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_mem_PG_of_minPenalty0_lt_top
-- name    : CondConvexRisk.Representation.mem_PG_of_minPenalty0_lt_top
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:56:41.30862+00:00
-- url     : https://prove2.me/theorems/199b1934-2a2e-404a-9fc2-b9411d42358c
-- title:
--   Proof of Theorem 3.2 — finite unconditional penalty forces $Q\in\mathcal P_{\mathcal G}$
-- statement:
--   Let $\rho:L^\infty\to L^\infty_{\mathcal G}$ be a conditional convex risk measure, $\rho_0(X)=E_P[\rho(X)]$, and $\alpha^*_0(Q)=\sup_{X\in L^\infty}\{-E_QX-\rho_0(X)\}$. If $Q$ is a probability measure with $Q\ll P$ and $\alpha^*_0(Q)<+\infty$, then
--   $$Q(A)=P(A)\quad\text{for every }A\in\mathcal G,$$
--   that is, $Q\in\mathcal P_{\mathcal G}$.
--
--   This is why only the models in $\mathcal P_{\mathcal G}$ enter the conditional representation.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 7, proof of Theorem 3.2 ("We now prove that if α*_0(Q) < +∞, then Q ∈ P_G")

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem mem_PG_of_minPenalty0_lt_top {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Q ≪ P)
    (hfin : minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Q < ⊤) :
    ∀ A : Set Ω, MeasurableSet[m] A → Q A = P A := by sorry

end CondConvexRisk.Representation
