-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlows_submodular_max_flow_min_cut
-- name    : DiscreteConvex.NetworkFlows.submodular_max_flow_min_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:16:13.241646+00:00
-- url     : https://prove2.me/theorems/8c535099-f90d-4865-9a7d-36eed288dcc1
-- title:
--   Theorem 9.13 -- max-flow min-cut theorem for submodular flows
-- statement:
--   **Theorem 9.13** (p.259), the max-flow min-cut theorem for submodular flows. For a feasible maximum submodular flow problem on a specified arc $a_0$, $\sup\{\xi(a_0) \mid \xi \text{ feasible}\} = \min\big(\bar c(a_0), \min_X\{\bar c(\Delta^-X) - \underline c(\Delta^+X\setminus\{a_0\}) + \rho(X) \mid a_0 \in \Delta^+X\}\big)$ (9.61), a common value in $\mathbb R \cup \{+\infty\}$. If $\bar c$, $\underline c$, and $\rho$ are integer valued and this value is finite, an integer-valued maximum flow exists.
--
--   **Formalization notes.** (1) The right-hand inner minimum is over $X$ with $a_0 \in \Delta^+X$; since $V$ is finite, this is a genuine finite `Finset.inf` over `Finset V` (with the empty-index convention $= \top$), not a general infimum, matching the book's own finite min over subsets of $V$. (2) The left-hand supremum is over the genuinely infinite set of real-valued feasible flows; `sSup` on `ℝ ∪ {+∞}` is used directly, which is well-behaved here because the feasible set is nonempty (`hfeas`) and bounded above by $\bar c(a_0)$, matching the book's use of `max` for this common value. (3) The integrality clause is stated as existence of an integer-valued flow that dominates every real-valued feasible flow at $a_0$ — i.e., an actual maximizer, not merely a flow attaining the value.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.259, Theorem 9.13.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.259, Theorem 9.13

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

/-- Theorem 9.13, the max-flow min-cut theorem for submodular flows (Murota, *Discrete Convex
Analysis*, SIAM 2003, p.259). For a feasible maximum submodular flow problem on a specified
arc `a0`,
`sup{ξ(a0) | ξ feasible} = min(c̄(a0), min_X{c̄(Δ⁻X) - c(Δ⁺X∖{a0}) + ρ(X) | a0 ∈ Δ⁺X})`
(9.61), a common value in `ℝ ∪ {+∞}`. If `c̄`, `c`, and `ρ` are integer valued and this value
is finite, an integer-valued maximum flow exists. -/
theorem submodular_max_flow_min_cut {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    [DecidableEq A] (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (ρ : Finset V → WithTop ℝ) (hρ : Submodular ρ) (hρEmpty : ρ ∅ = 0)
    (hρV : ρ (Finset.univ : Finset V) = 0) (a0 : A)
    (hfeas : ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) :
    (sSup {v : WithTop ℝ | ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ ∧
        v = (ξ a0 : WithTop ℝ)} =
      min (cUpper a0)
        ((Finset.univ.filter (fun X : Finset V => a0 ∈ DeltaPlus tail head X)).inf
          (fun X => UpperCapOf cUpper (DeltaMinus tail head X) +
            NegLowerCapOf cLower ((DeltaPlus tail head X).erase a0) + ρ X))) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → IsIntegerUpper ρ →
      (sSup {v : WithTop ℝ | ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ ∧
          v = (ξ a0 : WithTop ℝ)} ≠ ⊤) →
      ∃ ξ : A → ℤ, FeasibleFlowMSFP1 tail head cUpper cLower ρ (fun a => (ξ a : ℝ)) ∧
        ∀ ξ' : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ' → ξ' a0 ≤ (ξ a0 : ℝ)) := by sorry

end DiscreteConvex.NetworkFlows
