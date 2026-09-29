-- Prove2me | Theorems.Thm_ConjGrad_Termination_cg_terminates_in_n_steps
-- name    : ConjGrad.Termination.cg_terminates_in_n_steps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:53:00.506848+00:00
-- url     : https://prove2.me/theorems/9ca266c4-0b2f-456a-ab6e-847b23994bf1
-- title:
--   Theorems 4:2 and 5:2 — the cg-method reaches the solution in at most n steps
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k \in \mathbb{R}^n$, and let $h$ be the solution of $Ah = k$. Let $x_0 \in \mathbb{R}^n$ be an arbitrary initial estimate, and let $x_0, x_1, x_2, \dots$ be the estimates produced by the conjugate gradient method (3:1):
--   $$p_0 = r_0 = k - Ax_0,\quad a_i = \frac{|r_i|^2}{(p_i, Ap_i)},\quad x_{i+1} = x_i + a_i p_i,\quad r_{i+1} = r_i - a_i A p_i,\quad b_i = \frac{|r_{i+1}|^2}{|r_i|^2},\quad p_{i+1} = r_{i+1} + b_i p_i.$$
--   Then there is an $m$ with
--
--   $$m \le n \qquad\text{and}\qquad x_m = h.$$
--
--   This is the finite-termination property announced in the paper's abstract ("The solution is given in $n$ steps") and in Section 3: "If no rounding-off error is encountered, one will reach an estimate $x_m$ ($m \le n$) at which $r_m = 0$. This estimate is the desired solution $h$." It is Theorem 4:2 for the method of conjugate directions, applied to the cg-method by Theorem 5:2.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, the solution is given by the hypothesis $Ah = k$, and the iteration is total: Lean's division by zero makes it stay at $x_m$ once $r_m = 0$ (no stopping test and no reference to $h$ or $A^{-1}$ inside the iteration). Exact real arithmetic is assumed, as in the paper's "if no rounding-off errors are encountered".
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 409 (abstract: 'The solution is given in n steps'), p. 410 (Section 3: 'one will reach an estimate x_m (m ≦ n) at which r_m = 0. This estimate is the desired solution h'), p. 412 Theorem 4:2, p. 415 Theorem 5:2

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorems 4:2 and 5:2 (Hestenes–Stiefel 1952, pp. 410, 412, 415): for a symmetric
positive definite `n × n` matrix `A`, a right-hand side `k` with solution `h` (`Ah = k`) and
an arbitrary initial estimate `x₀`, the cg-method (3:1) reaches the solution after at most
`n` steps: some estimate `xₘ` with `m ≤ n` equals `h`. -/
theorem cg_terminates_in_n_steps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x₀ : Fin n → ℝ) :
    ∃ m ≤ n, (cgIter A k x₀ m).x = h := by sorry

end ConjGrad.Termination
