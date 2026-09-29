-- Prove2me | Theorems.Thm_ConjGrad_Termination_cd_terminates
-- name    : ConjGrad.Termination.cd_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:49:09.86534+00:00
-- url     : https://prove2.me/theorems/69a28aee-4ca6-48ff-a451-e1fdcdaa3cb3
-- title:
--   Theorem 4:2 — the cd-method reaches the solution in m ≤ n steps
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k \in \mathbb{R}^n$, and let $h$ be the solution of $Ah = k$. Let $x_i$, $r_i$, $p_i$ ($i = 0, 1, \dots$) be a run of the method of conjugate directions for $Ax = k$ (with an arbitrary initial estimate $x_0$ and arbitrary initial direction $p_0$), and suppose the directions $p_0, p_1, \dots, p_{n-1}$ are all nonzero. Then there is an $m$ with
--
--   $$m \le n \qquad\text{and}\qquad x_m = h.$$
--
--   In the paper's words, the cd-method is an $m$-step method ($m \le n$): at the $m$-th step the estimate $x_m$ is the desired solution $h$. Applied to the conjugate gradient method through Theorem 5:2, this gives the finite termination of that method.
--
--   **Formalization Note** The hypothesis that $p_0, \dots, p_{n-1}$ are nonzero is implicit in the paper's proof ("the vectors $p_0, p_1, \dots$ are linearly independent"); without it the statement fails (take $p_0 = 0$). The solution may be reached before step $n$, after which the remaining directions may still be nonzero; the statement only requires them nonzero, not the residuals.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 412, Theorem 4:2 and its proof; standing assumption (A symmetric positive definite) p. 410

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun

open Matrix

namespace ConjGrad.Termination

/-- Theorem 4:2 (Hestenes–Stiefel 1952, p. 412). The cd-method is an `m`-step method with
`m ≤ n`: for a symmetric positive definite `n × n` matrix `A`, the solution `h` of `Ah = k`,
and every run of the cd-method whose directions `p₀, …, pₙ₋₁` are nonzero, some estimate
`xₘ` with `m ≤ n` equals `h`. -/
theorem cd_terminates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p)
    (hp : ∀ i < n, p i ≠ 0) :
    ∃ m ≤ n, x m = h := by sorry

end ConjGrad.Termination
