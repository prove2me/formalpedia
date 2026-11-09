-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_theorem_3_11
-- name    : DetComplexityPowerSum.Quadratic.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:51.916273+00:00
-- url     : https://prove2.me/theorems/5f39463e-09ed-412e-8a37-8ba8093d42eb
-- title:
--   Theorem 3.11 — affine multi-homogeneous Bézout bound
-- statement:
--   Let $x_1,\dots,x_k$ be disjoint sets of variables with $|x_j|=n_j$, and let $P_1,\dots,P_N$ be polynomials over $\mathbb C$ in these variables with $N=n_1+\dots+n_k$, where $P_i$ has degree at most $d_{i,j}$ in the variables $x_j$. For every $i\in[N]$ define the linear form
--   $$d_i=d_{i,1}y_1+d_{i,2}y_2+\dots+d_{i,k}y_k.$$
--   Then the set of solutions of the system $\{P_i(x_1,\dots,x_k)=0: i\in[N]\}$ in $\mathbb C^N$ is either infinite, or has size at most $B$, where $B$ is the coefficient of the monomial $y_1^{n_1}y_2^{n_2}\cdots y_k^{n_k}$ in the polynomial $d_1d_2\cdots d_N$.
--
--   No assumption is made on the zeros: they need not be simple, and the polynomials need not be homogeneous. The source cites this affine form from Morgan and Sommese (1987). Applied to the block structure of the amended proxy system, it gives a much smaller bound than the classical Bézout theorem, which is what raises the lower bound to quadratic.
--
--   **Formalization Note** Blocks and equations are indexed by arbitrary finite types, of which $[k]$ and $[N]$ are the instance; `hN` is $N=\sum_j n_j$.
--
--   Differences from the source:
--   - generalization: $d_{i,j}$ is the degree of $P_i$ in $x_j$ → `hd` only requires the block degree to be at most $d_{i,j}$; reason: p. 8 defines multi-degree by "degree at most"; taking $d_{i,j}$ equal to the block degree gives the printed reading
--   - encoding: variable sets $x_1,\dots,x_k$ and polynomials $P_1,\dots,P_N$ → fibres of `Σ j, α j` over a finite type `κ`, and a finite type `E` of equations; reason: $\kappa=[k]$, $\alpha_j=[n_j]$, $E=[N]$ is the source's indexing
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 9, Theorem 3.11

import Mathlib
import Definitions.Def_DetComplexityPowerSum_Quadratic_BezoutNumber
open MvPolynomial

namespace DetComplexityPowerSum.Quadratic

theorem theorem_3_11 {κ E : Type*} {α : κ → Type*}
    [Fintype κ] [∀ j, Fintype (α j)] [Fintype E]
    (hN : Fintype.card E = ∑ j : κ, Fintype.card (α j))
    (P : E → MvPolynomial (Σ j, α j) ℂ) (d : E → κ → ℕ)
    (hd : ∀ (i : E) (j : κ), blockDegree (P i) j ≤ d i j) :
    {x : (Σ j, α j) → ℂ | ∀ i : E, eval x (P i) = 0}.Infinite ∨
      {x : (Σ j, α j) → ℂ | ∀ i : E, eval x (P i) = 0}.ncard ≤ bezoutNumber α d := by sorry

end DetComplexityPowerSum.Quadratic
