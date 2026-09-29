-- Prove2me | Theorems.Thm_BertsekasDP_discrete_minimum_principle
-- name    : BertsekasDP.discrete_minimum_principle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-07T15:48:12.289715+00:00
-- url     : https://prove2.me/theorems/be6ea235-deb3-44fe-9f5f-945b46e3ef1d
-- title:
--   Discrete-time Minimum Principle (Prop. 3.3.2)
-- statement:
--   **Proposition 3.3.2 (Discrete-Time Minimum Principle).** Consider the deterministic discrete-time problem of minimizing
--
--   $$g_N(x_N) + \sum_{k=0}^{N-1} g_k(x_k, u_k) \qquad \text{subject to} \qquad x_{k+1} = f_k(x_k,u_k), \quad x_0 \text{ given}, \quad u_k \in U_k,$$
--
--   with all $f_k$, $g_k$ and $g_N$ continuously differentiable and every constraint set $U_k$ **convex**. Suppose $(u_0^*, \dots, u_{N-1}^*)$ is optimal, with corresponding trajectory $(x_0^*, \dots, x_N^*)$. Define the stage Hamiltonians $H_k(x,u,p) = g_k(x,u) + \langle p, f_k(x,u)\rangle$ and the adjoint sequence backward by
--
--   $$p_N \;=\; \nabla g_N(x_N^*), \qquad p_k \;=\; \nabla_x H_k\bigl(x_k^*, u_k^*, p_{k+1}\bigr).$$
--
--   Then for every stage $k < N$ the variational inequality holds:
--
--   $$\bigl\langle \nabla_u H_k\bigl(x_k^*, u_k^*, p_{k+1}\bigr), \; u - u_k^* \bigr\rangle \;\ge\; 0 \qquad \text{for all } u \in U_k .$$
--
--   This is the discrete-time shadow of the Minimum Principle, and the natural warm-up target of this mission: it needs only finite-dimensional calculus, with no ODE theory, yet exhibits the same adjoint structure. Convexity of $U_k$ is what turns the first-order condition into a variational inequality over the whole constraint set; when $U_k = \mathbb{R}^m$ it reduces to stationarity, $\nabla_u H_k = 0$.
--
--   **Formalization Note** The conclusion is a variational inequality, strictly weaker than the statement that $u_k^*$ minimizes $H_k$ over $U_k$ — the source derives the minimization form only under the additional convexity of $H_k$ in $u$. Optimality is assumed against all feasible sequences with the same initial state. Gradients are Mathlib's, classical here since the data are $C^1$; with $N = 0$ every claim is vacuous.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 3.3.2

import Mathlib

namespace BertsekasDP

open scoped RealInnerProductSpace

theorem discrete_minimum_principle {n m N : ℕ}
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n))
    (g : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (gN : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : ℕ → Set (EuclideanSpace ℝ (Fin m)))
    (hUconv : ∀ k, Convex ℝ (U k))
    (hf : ∀ k, ContDiff ℝ 1 (Function.uncurry (f k)))
    (hg : ∀ k, ContDiff ℝ 1 (Function.uncurry (g k)))
    (hgN : ContDiff ℝ 1 gN)
    (x0 : EuclideanSpace ℝ (Fin n))
    (ustar : ℕ → EuclideanSpace ℝ (Fin m))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n))
    (hx0 : xstar 0 = x0)
    (hdyn : ∀ k < N, xstar (k + 1) = f k (xstar k) (ustar k))
    (humem : ∀ k < N, ustar k ∈ U k)
    (hopt : ∀ (u : ℕ → EuclideanSpace ℝ (Fin m))
      (x : ℕ → EuclideanSpace ℝ (Fin n)),
      x 0 = x0 → (∀ k < N, x (k + 1) = f k (x k) (u k)) →
      (∀ k < N, u k ∈ U k) →
      gN (xstar N) + ∑ k ∈ Finset.range N, g k (xstar k) (ustar k) ≤
        gN (x N) + ∑ k ∈ Finset.range N, g k (x k) (u k)) :
    ∃ p : ℕ → EuclideanSpace ℝ (Fin n),
      p N = gradient gN (xstar N) ∧
      (∀ k < N, p k =
        gradient (fun y => g k y (ustar k) + ⟪p (k + 1), f k y (ustar k)⟫)
          (xstar k)) ∧
      (∀ k < N, ∀ u ∈ U k,
        0 ≤ ⟪gradient
              (fun v => g k (xstar k) v + ⟪p (k + 1), f k (xstar k) v⟫)
              (ustar k),
            u - ustar k⟫) := by sorry

end BertsekasDP
