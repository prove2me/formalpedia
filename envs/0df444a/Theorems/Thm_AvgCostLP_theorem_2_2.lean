-- Prove2me | Theorems.Thm_AvgCostLP_theorem_2_2
-- name    : AvgCostLP.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:53.532785+00:00
-- url     : https://prove2.me/theorems/32bbf63c-310a-4c0e-8f63-c72a9325fd99
-- title:
--   Theorem 2.2 — (P) subconsistent with finite subvalue $\underline\rho$ ⟺ (P*) consistent with finite value $\underline\rho$
-- statement:
--   Consider the abstract linear programs (P) and (P*) of §2.2 in two dual pairs $(X,Y)$, $(Z,W)$, with $L:X\to Z$ linear, adjoint $L^*:W\to Y$, a nonempty convex cone $\Lambda\subset X$, $c\in Y$ and $b\in Z$. For every real $\underline\rho$:
--
--   $$\underline\rho=\inf\{r\mid(b,r)\in\overline H\}\ \text{(finite, and the set is nonempty)}\iff\underline\rho=\sup\{\langle b,w\rangle\mid -L^*w+c\in\Lambda^*\}\ \text{(finite, and the set is nonempty)},$$
--
--   where $\overline H$ is the closure of $H=\{(Lx,\langle x,c\rangle+r)\mid x\in\Lambda,r\ge0\}$ in $\sigma(Z\times\mathbb R,W\times\mathbb R)$. In words: (P) is subconsistent with a finite subvalue $\underline\rho$ if and only if (P*) is consistent with a finite value $\underline\rho$.
--
--   This is the duality theorem of Anderson and Nash [2, Thm. 3.3]; it reduces "no duality gap" to showing that one point of $\overline H$ lies in $H$.
--
--   **Formalization Note** Both sides are `IsGLB`/`IsLUB` statements over $\mathbb R$, which force the sets to be nonempty and the bounds finite.
--
--   Differences from the source:
--   - reading: σ(X,Y) is 'the coarsest topology under which |⟨·, y⟩| is continuous for every y' (p.7) → the coarsest topology making every ⟨·, y⟩ continuous; reason: read literally the topology does not separate x from −x, against the same paragraph; the net characterization ⟨x_i, y⟩ → ⟨x̄, y⟩ on p.7 fixes the usual weak topology
--   - reading: Λ a convex cone → Λ a nonempty convex cone; reason: with Λ = ∅ and b = 0 the set H is empty (not subconsistent) while every w is dual feasible with value 0, so the theorem needs Λ ≠ ∅; the paper's cones are nonempty
--   - encoding: L weakly continuous, with its weakly continuous adjoint L* (Prop. 2.1) → linear L and linear L* with ⟨x, L*w⟩ = ⟨Lx, w⟩ as data; reason: by Prop. 2.1, L is weakly continuous iff such an L* exists, and then L* is weakly continuous
--   - encoding: (P) subconsistent with a finite subvalue ρ̲; (P*) consistent with a finite value ρ̲ → IsGLB {r | (b, r) ∈ H̄} ρ̲ ↔ IsLUB {⟨b, w⟩ | w feasible} ρ̲; reason: over ℝ these say exactly that the sets are nonempty with finite infimum / supremum ρ̲
--   - generalization: Λ a convex cone, containing 0 like the paper's Λ = M⁺_w(Γ) → Mathlib ConvexCone, closed under addition and positive scalars, which need not contain 0; reason: every cone containing 0 is an instance; the theorem still holds because for x ∈ Λ the points (ε Lx, ε⟨x, c⟩) put 0 in the weak closure of H
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Theorem 2.2, p.9 (setting §2.2, pp.7-8)

import Mathlib
import Definitions.Def_AvgCostLP_LinearProgram
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Theorem 2.2, p.9 (subconsistency and duality [2, Thm. 3.3]): (P) is subconsistent
with a finite subvalue `ρ̲` if and only if (P*) is consistent with a finite value `ρ̲`.

For the abstract programs (2.2)–(2.3): `ρ̲` is the greatest lower bound of
`{r | (b, r) ∈ H̄}` (closure in `σ(Z × ℝ, W × ℝ)`) iff `ρ̲` is the least upper bound of the dual
objective values `{⟨b, w⟩ | −L*w + c ∈ Λ*}`. Over `ℝ`, `IsGLB`/`IsLUB` force the sets to be
nonempty and the bound finite.

**Formalization Note** The weak topology is the usual one (each `⟨·, (w, r')⟩` continuous); the
cone `Λ` is nonempty; `L*` with the adjoint identity is part of the data (Prop. 2.1). -/
theorem theorem_2_2 {X Y Z W : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup Z] [Module ℝ Z] [AddCommGroup W] [Module ℝ W]
    (P : LinearProgram X Y Z W) (ρ : ℝ) :
    IsGLB P.subvalueSet ρ ↔ IsLUB P.dualValueSet ρ := by sorry

end AvgCostLP
