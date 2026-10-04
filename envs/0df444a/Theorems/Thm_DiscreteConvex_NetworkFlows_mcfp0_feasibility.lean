-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlows_mcfp0_feasibility
-- name    : DiscreteConvex.NetworkFlows.mcfp0_feasibility
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:17:13.024718+00:00
-- url     : https://prove2.me/theorems/2956d03e-0294-4dd9-a34f-763a9386fe99
-- title:
--   Theorem 9.3 -- feasibility of the minimum cost flow problem
-- statement:
--   **Theorem 9.3** (p.248). For $\bar c : A \to \mathbb R \cup \{+\infty\}$, $\underline c : A \to \mathbb R \cup \{-\infty\}$, and $x : V \to \mathbb R$, there exists a flow $\xi : A \to \mathbb R$ satisfying the capacity constraint (9.12) and $\partial\xi = x$ (9.13) if and only if $x(X) \le \kappa(X)$ for all $X \subseteq V$ and $x(V) = 0$ (9.17). If $\bar c$, $\underline c$, and $x$ are integer valued and the problem is feasible, an integer-valued feasible flow exists (9.19).
--
--   **Formalization note.** The restatement of (9.17) as an equality of sets, $B(\kappa) = \{\partial\xi \mid \ldots\}$ (Eq. (9.18)), is not drafted as a separate object — this item states the iff directly, and the integer refinement (9.19) as a second conjunct — since introducing a named base-polyhedron object purely to restate the same content would add no further claim.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248, Theorem 9.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248, Theorem 9.3

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlows_CutCapacity
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower

namespace DiscreteConvex.NetworkFlows

/-- Theorem 9.3, feasibility (Murota, *Discrete Convex Analysis*, SIAM 2003, p.248). For
`c̄ : A → ℝ ∪ {+∞}`, `c : A → ℝ ∪ {-∞}`, and `x : V → ℝ`, there exists a flow `ξ : A → ℝ`
satisfying the capacity constraint (9.12) and `∂ξ = x` (9.13) if and only if `x(X) ≤ κ(X)`
for all `X ⊆ V` and `x(V) = 0`. If `c̄` and `c` are integer valued, `x` is integer valued, and
the problem is feasible, an integer-valued feasible flow exists. -/
theorem mcfp0_feasibility {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (x : V → ℝ) :
    ((∃ ξ : A → ℝ, FeasibleFlowMCFP0 tail head cUpper cLower x ξ) ↔
      ((∀ X : Finset V,
          ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ CutCapacity tail head cUpper cLower X) ∧
        (∑ v : V, x v) = 0)) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → (∀ v : V, ∃ n : ℤ, (n : ℝ) = x v) →
      (∃ ξ : A → ℝ, FeasibleFlowMCFP0 tail head cUpper cLower x ξ) →
      ∃ ξ : A → ℤ, FeasibleFlowMCFP0 tail head cUpper cLower x (fun a => (ξ a : ℝ))) := by sorry

end DiscreteConvex.NetworkFlows
