-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDuality_Lagrange_lagrangian_kernel_recovers_F
-- name    : DiscreteConvex.ConjugacyDuality.Lagrange.lagrangian_kernel_recovers_F
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:13:29.39204+00:00
-- url     : https://prove2.me/theorems/a5d5a1d6-1160-4c7f-a953-4eed25c6e056
-- title:
--   Proposition 8.51(1)-(2) -- the kernel recovers F and the primal objective
-- statement:
--   **Proposition 8.51**, parts (1)-(2) (p.236). Assuming the perturbation $F$ is self-biconjugate in its second argument ($F(x,\cdot)^{\bullet\bullet}=F(x,\cdot)$, Eq. (8.55)): (1) $F(x,u) = \sup\{K(x,y) - \langle u,y\rangle : y \in \mathbb Z^U\}$ for all $x,u$; (2) $f(x) = \sup\{K(x,y) : y \in \mathbb Z^U\}$ for all $x$ (the case $u=0$ of (1)). These identities are the direct algebraic ingredient of the saddle-point theorem's own proof.
--
--   **Formalization Note.** Part (3)-(6) of the book's Theorem 8.53 (a further biconjugacy identity chain for the optimal-value function $\phi$) is not drafted in this mission; it would need an `EReal`-domain Legendre-Fenchel transform not otherwise built here, since $\phi$ can genuinely take the value $-\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Proposition 8.51(1)-(2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Proposition 8.51(1)-(2)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- Proposition 8.51, parts (1)-(2) (Murota, *Discrete Convex Analysis*, SIAM 2003, p.236).
Assuming the perturbation `F` is self-biconjugate in its second argument (`F(x,·)•• = F(x,·)`,
Eq. (8.55)): (1) `F(x,u) = sup\{K(x,y) - ⟨u,y⟩ : y ∈ Z^U\}` for all `x, u`; (2)
`f(x) = sup\{K(x,y) : y ∈ Z^U\}` for all `x` (the case `u = 0` of (1), using `F(x,0) = f(x)`). -/
theorem lagrangian_kernel_recovers_F {V U : Type*} [Fintype U] [DecidableEq U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ)
    (hF : ∀ x : V → ℤ, ConvexConjugate (ConvexConjugate (F x)) = F x) :
    (∀ x : V → ℤ, ∀ u : U → ℤ,
        ToEReal (F x u) = sSup {v : EReal | ∃ y : U → ℤ,
          v = LagrangianKernel F x y - ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}) ∧
    (∀ x : V → ℤ,
        ToEReal (PrimalValue F x) =
          sSup {v : EReal | ∃ y : U → ℤ, v = LagrangianKernel F x y}) := by sorry

end DiscreteConvex.ConjugacyDuality.Lagrange
