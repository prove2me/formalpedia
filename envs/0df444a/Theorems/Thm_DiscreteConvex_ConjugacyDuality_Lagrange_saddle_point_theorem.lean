-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDuality_Lagrange_saddle_point_theorem
-- name    : DiscreteConvex.ConjugacyDuality.Lagrange.saddle_point_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:16:38.023999+00:00
-- url     : https://prove2.me/theorems/fab4ec3e-ed2b-4081-90bf-51f86080fe15
-- title:
--   Theorem 8.54 -- the saddle-point theorem
-- statement:
--   **Theorem 8.54** (p.238). Assuming the perturbation $F$ is self-biconjugate in its second argument (Eq. (8.55)): both $\inf(P)$ and $\sup(D)$ are finite and $\min(P)=\max(D)$ if and only if there exist $\bar x \in \mathbb Z^V$ and $\bar y \in \mathbb Z^U$ such that $K(\bar x,\bar y)$ is finite and $K(x,\bar y) \le K(\bar x,\bar y) \le K(\bar x,y)$ for all $x \in \mathbb Z^V$, $y \in \mathbb Z^U$; in this case $\bar x \in \operatorname{opt}(P)$ and $\bar y \in \operatorname{opt}(D)$.
--
--   This is a completely general saddle-point characterization of strong duality for the abstract perturbation-based Lagrangian framework, requiring no M-convexity of the primal problem at all — the book uses it (specialized to M-convex programs via a particular choice of perturbation, not drafted in this mission) to prove strong duality for M-convex Lagrangian optimization, but the theorem itself is the general min-max characterization underlying that specialization.
--
--   **Formalization Note.** "Finite" is `≠ ⊤ ∧ ≠ ⊥` in `EReal`; the conclusion's witnesses $\bar x, \bar y$ are additionally asserted to be primal/dual optimal, matching the book's own "If this is the case, we have..." remark, not left as a separate corollary.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.238, Theorem 8.54.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.238, Theorem 8.54

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptD

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- Theorem 8.54, the saddle-point theorem (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.238). Assuming the perturbation `F` is self-biconjugate in its second argument
(Eq. (8.55)): both `inf(P)` and `sup(D)` are finite and `min(P) = max(D)` if and only if there
exist `x̄ ∈ Zⱽ` and `ȳ ∈ Z^U` such that `K(x̄,ȳ)` is finite and
`K(x,ȳ) ≤ K(x̄,ȳ) ≤ K(x̄,y)` for all `x ∈ Zⱽ, y ∈ Z^U`; in this case `x̄ ∈ opt(P)` and
`ȳ ∈ opt(D)`. The page writes `min(P) = max(D)`: both values are finite **and attained**, which
is why `opt(P)` and `opt(D)` are required nonempty. Equality of a finite infimum and supremum
alone does not give a saddle point (`F(x,u) = 2^{-x} + |u|` on one coordinate each has
`inf(P) = sup(D) = 0`, attained nowhere, and no saddle point exists). -/
theorem saddle_point_theorem {V U : Type*} [Fintype U] [DecidableEq U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ)
    (hF : ∀ x : V → ℤ, ConvexConjugate (ConvexConjugate (F x)) = F x) :
    ((OptP F).Nonempty ∧ (OptD F).Nonempty ∧
        InfP F ≠ ⊤ ∧ InfP F ≠ ⊥ ∧ SupD F ≠ ⊤ ∧ SupD F ≠ ⊥ ∧ InfP F = SupD F) ↔
      (∃ xbar : V → ℤ, ∃ ybar : U → ℤ,
        LagrangianKernel F xbar ybar ≠ ⊤ ∧ LagrangianKernel F xbar ybar ≠ ⊥ ∧
        (∀ x : V → ℤ, LagrangianKernel F x ybar ≤ LagrangianKernel F xbar ybar) ∧
        (∀ y : U → ℤ, LagrangianKernel F xbar ybar ≤ LagrangianKernel F xbar y) ∧
        xbar ∈ OptP F ∧ ybar ∈ OptD F) := by sorry

end DiscreteConvex.ConjugacyDuality.Lagrange
