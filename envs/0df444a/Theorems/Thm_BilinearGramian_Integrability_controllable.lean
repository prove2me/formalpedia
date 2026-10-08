-- Prove2me | Theorems.Thm_BilinearGramian_Integrability_controllable
-- name    : BilinearGramian.Integrability.controllable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:59.307331+00:00
-- url     : https://prove2.me/theorems/1050e174-e7b7-4e9c-8770-2e6002eded32
-- title:
--   Example 3.3 — the example system is locally controllable: (A, b) is controllable
-- statement:
--   Let $A = \operatorname{diag}(-1,-2)$ and $b = (1,1)^T$ be the data of Example 3.3. The pair $(A, b)$ is controllable: the Kalman matrix
--   $$[\,b \;\; Ab\,] = \begin{bmatrix} 1 & -1 \\ 1 & -2 \end{bmatrix}$$
--   has rank $2$. By the paper's definition (p. 694), the bilinear system of Example 3.3 is therefore **locally controllable**, for every value of $\nu$.
--
--   This is the hypothesis under which the gradient formula (3.8) was claimed, so it makes Example 3.3 a counterexample within the claim's scope.
--
--   **Formalization Note** Controllability is stated as: the only $v \in \mathbb R^2$ with $v^T A^k b = 0$ for $k = 0, 1$ is $v = 0$.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 694 (definition) and p. 697, Example 3.3 ("a locally controllable system")

import Mathlib
import Definitions.Def_BilinearGramian_Integrability_LinGramian
import Definitions.Def_BilinearGramian_Integrability_Example33

open Matrix

namespace BilinearGramian.Integrability

/-- Example 3.3 (Benner–Damm 2011, p. 697, with the definition of local controllability on
p. 694): the system of Example 3.3 is locally controllable, i.e. the pair
`(A, b) = (diag(-1, -2), (1, 1)ᵀ)` is controllable. -/
theorem controllable : IsControllable exA exB := by sorry

end BilinearGramian.Integrability
