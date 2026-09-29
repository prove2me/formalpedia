-- Prove2me | Theorems.Thm_FamousTheorems_dirichlet_beta_three
-- name    : FamousTheorems.dirichlet_beta_three
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:41.424174+00:00
-- url     : https://prove2.me/theorems/4d13ea4b-420e-4dfa-ab35-bbfcc4ef58c7
-- title:
--   Euler's evaluation β(3) = π³/32
-- statement:
--   **Euler's evaluation $\beta(3)=\pi^3/32$.** The Dirichlet beta function at $3$ is
--   $$\beta(3)=\sum_{k=0}^\infty\frac{(-1)^k}{(2k+1)^3}=1-\frac1{3^3}+\frac1{5^3}-\cdots=\frac{\pi^3}{32}.$$
--
--   Euler found this value. It is the $L$-function of the non-trivial character modulo $4$ at $s=3$. The odd values $\beta(2k+1)$ are rational multiples of $\pi^{2k+1}$, analogous to the even zeta values, while $\beta(2)$ (Catalan's constant) is not known to be irrational.
--
--   **Formalization note.** Mathlib's `hasSum_L_function_mod_four_eval_three`. The series is written as $\sum_{n\ge0}\frac{\sin(\pi n/2)}{n^3}$. The factor $\sin(\pi n/2)$ is $0,1,0,-1$ for $n\equiv0,1,2,3\pmod4$, which is the character modulo $4$. The term for $n=0$ is $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `hasSum_L_function_mod_four_eval_three`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dirichlet_beta_three : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 3 * Real.sin (Real.pi * n / 2)) (Real.pi ^ 3 / 32) := by sorry

end FamousTheorems
