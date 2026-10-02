-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlows_msfp1_feasibility
-- name    : DiscreteConvex.NetworkFlows.msfp1_feasibility
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:16:40.581235+00:00
-- url     : https://prove2.me/theorems/19d0b7c9-6725-43d2-93d5-2ae9c156009b
-- title:
--   Theorem 9.10 -- feasibility of the submodular flow problem
-- statement:
--   **Theorem 9.10** (p.258). A submodular flow problem MSFP1 (upper capacity $\bar c$, lower capacity $\underline c$, submodular $\rho$ with $\rho(\emptyset) = \rho(V) = 0$) is feasible if and only if $\bar c(\Delta^-X) - \underline c(\Delta^+X) + \rho(X) \ge 0$ for all $X \subseteq V$ (9.54). If $\bar c$, $\underline c$, and $\rho$ are integer valued and the problem is feasible, an integer-valued feasible flow exists.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.258, Theorem 9.10.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.258, Theorem 9.10

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMSFP1
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaPlus
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaMinus
import Definitions.Def_DiscreteConvex_NetworkFlows_UpperCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_Submodular
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower

namespace DiscreteConvex.NetworkFlows

/-- Theorem 9.10, feasibility (Murota, *Discrete Convex Analysis*, SIAM 2003, p.258). A
submodular flow problem MSFP1 (upper capacity `c̄`, lower capacity `c`, submodular `ρ` with
`ρ(∅) = ρ(V) = 0`) is feasible if and only if `c̄(Δ⁻X) - c(Δ⁺X) + ρ(X) ≥ 0` for all `X ⊆ V`
(9.54). If `c̄`, `c`, and `ρ` are integer valued and the problem is feasible, an
integer-valued feasible flow exists. -/
theorem msfp1_feasibility {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (ρ : Finset V → WithTop ℝ) (hρ : Submodular ρ) (hρEmpty : ρ ∅ = 0)
    (hρV : ρ (Finset.univ : Finset V) = 0) :
    ((∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) ↔
      (∀ X : Finset V,
        UpperCapOf cUpper (DeltaMinus tail head X) +
            NegLowerCapOf cLower (DeltaPlus tail head X) + ρ X ≥ 0)) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → IsIntegerUpper ρ →
      (∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) →
      ∃ ξ : A → ℤ, FeasibleFlowMSFP1 tail head cUpper cLower ρ (fun a => (ξ a : ℝ))) := by sorry

end DiscreteConvex.NetworkFlows
