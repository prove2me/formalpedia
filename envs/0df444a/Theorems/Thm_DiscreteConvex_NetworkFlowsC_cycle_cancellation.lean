-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsC_cycle_cancellation
-- name    : DiscreteConvex.NetworkFlowsC.cycle_cancellation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:46.376989+00:00
-- url     : https://prove2.me/theorems/52e5c4c1-e22a-4aa9-8bb4-51b95168636d
-- title:
--   Theorem 9.22 -- cycle_cancellation
-- statement:
--   **Theorem 9.22** (p.265). For a feasible integer flow $\xi$ to MSFP2, cancelling a smallest negative cycle $Q$ produces a feasible integer flow $\bar\xi$ with a strictly improved objective: $\Gamma_2(\bar\xi)\le\Gamma_2(\xi)+\ell_\xi(Q)<\Gamma_2(\xi)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, Theorem 9.22.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, Theorem 9.22

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FeasibleFlowMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsC_Gamma2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxTailMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxHeadMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxActiveMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxLengthMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsC_CycleLength
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsSmallestNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ModifiedFlow

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.22 (p.265). For a feasible integer flow `ξ` to MSFP2, cancelling a smallest
negative cycle `Q` produces a feasible integer flow `ξ̄` with a strictly improved objective,
`Γ2(ξ̄) ≤ Γ2(ξ) + ℓξ(Q) < Γ2(ξ)`. The book's MSFP2 with (9.72) has `f` M-convex and integer
capacities; without M-convexity, `V = {u,v}`, no arcs and `f(0) = 0`, `f(±(χv - χu)) = -1` make the
two `C` arcs the smallest negative cycle while `Γ2` is unchanged, and with an upper capacity of
`1/2` the cancelled flow is infeasible. -/
theorem cycle_cancellation (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hcUpperZ : ∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n : ℝ) : WithTop ℝ))
    (hcLowerZ : ∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n : ℝ) : WithBot ℝ)) (xi : A → ℤ)
    (hfeas : FeasibleFlowMSFP2Z tail head cUpper cLower f xi) (k : ℕ)
    (a : Fin (k+1) → (A ⊕ A ⊕ (V × V)))
    (hsmallest : IsSmallestNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
      (AuxActiveMSFP2Z tail head cUpper cLower f xi) (AuxLengthMSFP2Z tail head gamma f xi) k a) :
    FeasibleFlowMSFP2Z tail head cUpper cLower f (ModifiedFlow tail head k a xi) ∧
    Gamma2Z tail head gamma f (ModifiedFlow tail head k a xi) ≤
      Gamma2Z tail head gamma f xi + CycleLength (AuxLengthMSFP2Z tail head gamma f xi) k a ∧
    Gamma2Z tail head gamma f xi + CycleLength (AuxLengthMSFP2Z tail head gamma f xi) k a <
      Gamma2Z tail head gamma f xi := by sorry

end DiscreteConvex.NetworkFlowsC
