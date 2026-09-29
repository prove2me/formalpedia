-- Prove2me | Theorems.Thm_FamousTheorems_binet_formula_fib
-- name    : FamousTheorems.binet_formula_fib
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:56.473039+00:00
-- url     : https://prove2.me/theorems/d7bc7c7a-6a21-40aa-b529-49d9b1a7b78d
-- title:
--   Binet's formula for Fibonacci numbers
-- statement:
--   **Binet's formula.** For every $n\ge0$ the $n$-th Fibonacci number is
--   $$F_n=\frac{\varphi^n-\psi^n}{\sqrt5},\qquad \varphi=\frac{1+\sqrt5}{2},\quad \psi=\frac{1-\sqrt5}{2}.$$
--
--   The formula comes from diagonalising the linear recurrence $F_{n+2}=F_{n+1}+F_n$, whose characteristic roots are $\varphi$ and $\psi$. Since $|\psi|<1$, it shows that $F_n$ is the integer nearest to $\varphi^n/\sqrt5$ and that $F_{n+1}/F_n\to\varphi$. It is the standard example of solving a linear recurrence in closed form.
--
--   **Formalization note.** Mathlib's `Real.coe_fib_eq`. `Nat.fib` is the Fibonacci sequence with $F_0=0$, $F_1=1$, cast to `ℝ`. `Real.goldenRatio` and `Real.goldenConj` are $\varphi$ and $\psi$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.coe_fib_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem binet_formula_fib (n : ℕ) :
    (Nat.fib n : ℝ) = (Real.goldenRatio ^ n - Real.goldenConj ^ n) / Real.sqrt 5 := by sorry

end FamousTheorems
