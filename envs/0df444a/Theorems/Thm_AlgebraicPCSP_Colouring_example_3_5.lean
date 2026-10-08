-- Prove2me | Theorems.Thm_AlgebraicPCSP_Colouring_example_3_5
-- name    : AlgebraicPCSP.Colouring.example_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:29.23431+00:00
-- url     : https://prove2.me/theorems/5c878813-04e2-4a89-9c9e-436cd9eb3430
-- title:
--   Example 3.5 — the Olšák minor condition fails in Pol(H₂, H_k) for every k ≥ 2
-- statement:
--   Let $k \ge 2$ and let $\mathscr H_k = \mathrm{Pol}(\mathbf H_2, \mathbf H_k)$ be the minion of polymorphisms from the Boolean not-all-equal structure $\mathbf H_2$ to $\mathbf H_k = (E_k; \mathrm{NAE}_k)$. Consider the minor condition in a binary symbol $f$ and a 6-ary symbol $g$:
--   $$
--   \begin{aligned}
--   f(x, y) &\approx g(x, x, y, y, y, x),\\
--   f(x, y) &\approx g(x, y, x, y, x, y),\\
--   f(x, y) &\approx g(y, x, x, x, y, y).
--   \end{aligned}
--   $$
--   It is not satisfied in $\mathscr H_k$: there are no binary $f \in \mathscr H_k$ and 6-ary $g \in \mathscr H_k$ such that the three identities hold for all $x, y \in \{0, 1\}$.
--
--   The columns of the right-hand sides are exactly the six triples of $\mathrm{NAE}_2$. This is the obstruction behind Theorem 6.2: a minion homomorphism into $\mathscr H_K$ cannot exist from a minion satisfying this condition.
--
--   **Formalization Note** The condition is stated literally with separate $f$ and $g$. It is equivalent to $\mathscr H_k$ containing an Olšák function (Definition 6.1, as restated on p. 37 with $t, o$ in place of $f, g$).
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, pp. 16–17, Example 3.5 (restated p. 37)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures

namespace AlgebraicPCSP.Colouring

open PCSPBLPAff.Symmetric

/-- Example 3.5 (arXiv:1811.00970v3, pp. 16–17): for every `k ≥ 2` the minor condition
`f(x, y) ≈ g(x, x, y, y, y, x)`, `f(x, y) ≈ g(x, y, x, y, x, y)`, `f(x, y) ≈ g(y, x, x, x, y, y)`
is not satisfied in `Pol(H₂, H_k)`: there are no binary `f` and 6-ary `g` in `Pol(H₂, H_k)`
satisfying the three identities for all `x, y ∈ E₂`. -/
theorem example_3_5 (k : ℕ) (hk : 2 ≤ k) :
    ¬ ∃ f ∈ (HMinion k hk).mem 2, ∃ g ∈ (HMinion k hk).mem 6, ∀ x y : Fin 2,
      f ![x, y] = g ![x, x, y, y, y, x] ∧ f ![x, y] = g ![x, y, x, y, x, y] ∧
        f ![x, y] = g ![y, x, x, x, y, y] := by sorry

end AlgebraicPCSP.Colouring
