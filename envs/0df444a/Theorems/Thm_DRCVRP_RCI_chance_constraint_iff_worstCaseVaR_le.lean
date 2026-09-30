-- Prove2me | Theorems.Thm_DRCVRP_RCI_chance_constraint_iff_worstCaseVaR_le
-- name    : DRCVRP.RCI.chance_constraint_iff_worstCaseVaR_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:22:01.714753+00:00
-- url     : https://prove2.me/theorems/4bd8cf54-eef7-4ccf-a993-03b4a604af65
-- title:
--   Distributionally robust chance constraint $\iff$ worst-case VaR bound, Eq. (1)
-- statement:
--   Let $\mathcal P$ be a nonempty set of probability distributions of the demand vector $\tilde{\boldsymbol q}\in\mathbb R^n$, let $\epsilon\in(0,1)$, $Q\in\mathbb R$, and let $\mathbf R_k$ be a route, a list of distinct customers. Assume the values $\mathbb P\text{-VaR}_{1-\epsilon}[\sum_{i\in\mathbf R_k}\tilde q_i]$, $\mathbb P\in\mathcal P$, are bounded above. Then
--   $$
--   \mathbb P\big[\mathbf R_k\in\mathcal R(\tilde{\boldsymbol q})\big]\ge1-\epsilon\ \ \forall\mathbb P\in\mathcal P
--   \iff \mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in\mathbf R_k}\tilde q_i\Big]\le Q\ \ \forall\mathbb P\in\mathcal P
--   \iff \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in\mathbf R_k}\tilde q_i\Big]\le Q ,
--   $$
--   where $\mathbf R_k\in\mathcal R(\boldsymbol q)$ means $\sum_{i\in\mathbf R_k}q_i\le Q$.
--
--   A route satisfies its distributionally robust chance constraint exactly when the worst-case value-at-risk of its cumulative demand fits into one vehicle; this is what motivates the demand estimator (2).
--
--   **Formalization Note** The statement is the conjunction of the first-and-second and the first-and-third equivalences. The supremum is a real `sSup`; nonemptiness and boundedness above of the VaR values make it the paper's finite supremum (for an empty $\mathcal P$ the paper's supremum is $-\infty$, which a real `sSup` cannot represent). The route is a `List (Fin n)` without duplicates, and the sum over the route is the sum over its underlying finite set.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 721, Eq. (1)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_DRCVRP_RCI_Formulations

open MeasureTheory

namespace DRCVRP.RCI

/-- Eq. (1), §3, p. 721: for a route `R_k` (a list of distinct customers) and an ambiguity set
`𝒫` (`Amb`) of probability distributions of the demand vector,
`ℙ[R_k ∈ ℛ(q̃)] ≥ 1 - ε ∀ ℙ ∈ 𝒫 ⟺ ℙ-VaR_{1-ε}[∑_{i ∈ R_k} q̃_i] ≤ Q ∀ ℙ ∈ 𝒫
⟺ sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ R_k} q̃_i] ≤ Q`.
The supremum is a real `sSup`; `Amb` nonempty and the VaR values bounded above make it the
paper's (finite) supremum. -/
theorem chance_constraint_iff_worstCaseVaR_le {n : ℕ} (Amb : Set (Measure (Fin n → ℝ)))
    (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P) (hne : Amb.Nonempty)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (Q : ℝ) (r : List (Fin n)) (hr : r.Nodup)
    (hbdd : BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ r.toFinset, q i) (1 - ε)) '' Amb)) :
    (RouteChanceFeasible Amb ε Q r ↔
      ∀ P ∈ Amb, MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ r.toFinset, q i) (1 - ε) ≤ Q) ∧
    (RouteChanceFeasible Amb ε Q r ↔ worstCaseVaR Amb ε r.toFinset ≤ Q) := by sorry

end DRCVRP.RCI
